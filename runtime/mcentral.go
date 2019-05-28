// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The MCentral doesn't actually contain the list of free objects; the MSpan does.
// Each MCentral is two lists of MSpans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

import "runtime/internal/atomic"

// Central list of free objects of a given size.
//
//go:notinheap
type mcentral struct {
	lock      mutex
	spanclass spanClass // 当前mcentral的spanclass
	nonempty  mSpanList // 有空闲object的span列表 //list of spans with a free object, ie a nonempty free list
	empty     mSpanList // 没有空闲object（或者是在mcache中使用)的span列表 //list of spans with no free objects (or cached in an mcache)

	// nmalloc is the cumulative count of objects allocated from
	// this mcentral, assuming all spans in mcaches are
	// fully-allocated. Written atomically, read under STW.
	nmalloc uint64 // 历史分配过的对象数量
}

// Initialize a single central free list.
func (c *mcentral) init(spc spanClass) {
	c.spanclass = spc
	c.nonempty.init()
	c.empty.init()
}

// Allocate a span to use in an MCache.
// 分配一个span给mcache使用
// 分配给mcache的span仍然存在于mcentral.empty链表里
// 分配过程:
//   1.尝试从mcentral.nonempty链表里获取
//   2.尝试从mcentral.empty链表里获取
//   3.尝试从mheap里获取
func (c *mcentral) cacheSpan() *mspan {
	// Deduct credit for this span allocation and sweep if necessary.
	spanBytes := uintptr(class_to_allocnpages[c.spanclass.sizeclass()]) * _PageSize // 要分配的span的大小
	deductSweepCredit(spanBytes, 0)

	lock(&c.lock)
	traceDone := false
	if trace.enabled {
		traceGCSweepStart()
	}
	sg := mheap_.sweepgen
retry:
	// 从nonempty列表里找可用的span
	var s *mspan
	for s = c.nonempty.first; s != nil; s = s.next {
		// 需要清理的span
		if s.sweepgen == sg-2 && atomic.Cas(&s.sweepgen, sg-2, sg-1) {
			c.nonempty.remove(s)
			c.empty.insertBack(s)
			unlock(&c.lock)
			s.sweep(true) // 只初始化span
			goto havespan
		}
		// 忽略正在清理的span
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// we have a nonempty span that does not require sweeping, allocate from it
		// c.nonempty里有span的话就从c.nonempty里取出来放到c.empty里
		c.nonempty.remove(s)
		c.empty.insertBack(s)
		unlock(&c.lock)
		goto havespan
	}
	// 尝试从empty列表里清理出一个可用的span
	for s = c.empty.first; s != nil; s = s.next {
		// 需要清理的span
		if s.sweepgen == sg-2 && atomic.Cas(&s.sweepgen, sg-2, sg-1) {
			// we have an empty span that requires sweeping,
			// sweep it and see if we can free some space in it
			c.empty.remove(s)
			// swept spans are at the end of the list
			c.empty.insertBack(s)
			unlock(&c.lock)
			s.sweep(true) // 只初始化span
			freeIndex := s.nextFreeIndex()
			if freeIndex != s.nelems {
				s.freeindex = freeIndex
				goto havespan
			}
			lock(&c.lock)
			// the span is still empty after sweep
			// it is already in the empty list, so just retry
			goto retry
		}
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// already swept empty span,
		// all subsequent ones must also be either swept or in process of sweeping
		break
	}
	if trace.enabled {
		traceGCSweepDone()
		traceDone = true
	}
	unlock(&c.lock)

	// Replenish central list if empty.
	// 两个链表都没有可用span，则从mheap里获取一个
	s = c.grow()
	if s == nil {
		return nil
	}
	lock(&c.lock)
	c.empty.insertBack(s)
	unlock(&c.lock)

	// At this point s is a non-empty span, queued at the end of the empty list,
	// c is unlocked.
havespan:
	if trace.enabled && !traceDone {
		traceGCSweepDone()
	}
	cap := int32((s.npages << _PageShift) / s.elemsize)
	n := cap - int32(s.allocCount)
	if n == 0 || s.freeindex == s.nelems || uintptr(s.allocCount) == s.nelems {
		throw("span has no free objects")
	}
	// Assume all objects from this span will be allocated in the
	// mcache. If it gets uncached, we'll adjust this.
	atomic.Xadd64(&c.nmalloc, int64(n))
	usedBytes := uintptr(s.allocCount) * s.elemsize                       // span上面已被使用的字节数
	atomic.Xadd64(&memstats.heap_live, int64(spanBytes)-int64(usedBytes)) // 计算并记录未被使用的字节数
	if trace.enabled {
		// heap_live changed.
		traceHeapAlloc()
	}
	if gcBlackenEnabled != 0 {
		// heap_live changed.
		gcController.revise()
	}
	s.incache = true
	freeByteBase := s.freeindex &^ (64 - 1)
	whichByte := freeByteBase / 8
	// Init alloc bits cache.
	s.refillAllocCache(whichByte)

	// Adjust the allocCache so that s.freeindex corresponds to the low bit in
	// s.allocCache.
	s.allocCache >>= s.freeindex % 64

	return s
}

// Return span from an MCache.
func (c *mcentral) uncacheSpan(s *mspan) {
	lock(&c.lock)

	s.incache = false

	if s.allocCount == 0 {
		throw("uncaching span but s.allocCount == 0")
	}

	cap := int32((s.npages << _PageShift) / s.elemsize) // 计算span的最大object数量
	n := cap - int32(s.allocCount)                      // 计算未分配出去的object数量
	if n > 0 {
		c.empty.remove(s)
		c.nonempty.insert(s)
		// mCentral_CacheSpan conservatively counted
		// unallocated slots in heap_live. Undo this.
		atomic.Xadd64(&memstats.heap_live, -int64(n)*int64(s.elemsize))
		// cacheSpan updated alloc assuming all objects on s
		// were going to be allocated. Adjust for any that
		// weren't.
		atomic.Xadd64(&c.nmalloc, -int64(n))
	}
	unlock(&c.lock)
}

// freeSpan updates c and s after sweeping s.
// It sets s's sweepgen to the latest generation,
// and, based on the number of free objects in s,
// moves s to the appropriate list of c or returns it
// to the heap.
// freeSpan returns true if s was returned to the heap.
// If preserve=true, it does not move s (the caller
// must take care of it).
// 如果返还给heap则方法返回true
func (c *mcentral) freeSpan(s *mspan, preserve bool, wasempty bool) bool {
	if s.incache {
		throw("freeSpan given cached span")
	}
	s.needzero = 1

	if preserve {
		// preserve is set only when called from MCentral_CacheSpan above,
		// the span must be in the empty list.
		if !s.inList() {
			throw("can't preserve unlinked span")
		}
		atomic.Store(&s.sweepgen, mheap_.sweepgen)
		return false
	}

	lock(&c.lock)

	// Move to nonempty if necessary.
	if wasempty {
		c.empty.remove(s)
		c.nonempty.insert(s)
	}

	// delay updating sweepgen until here. This is the signal that
	// the span may be used in an MCache, so it must come after the
	// linked list operations above (actually, just after the
	// lock of c above.)
	atomic.Store(&s.sweepgen, mheap_.sweepgen) // 标记span的清扫状态为已清扫完毕，可用于再分配

	if s.allocCount != 0 { // 如果span中还有使用中的object则return false，表示不需要返回给heap
		unlock(&c.lock)
		return false
	}

	c.nonempty.remove(s) // 如果从未分配过内存，则返还给heap
	unlock(&c.lock)
	mheap_.freeSpan(s, 0) // 返还给mheap
	return true
}

// grow allocates a new empty span from the heap and initializes it for c's size class.
// 内存按pase size增长。
// 从这里开始转换为page(也就是内存页的概念)进行内存分配，是因为mheap是对应系统的内存管理的，系统内存管理是通过分页管理的。
func (c *mcentral) grow() *mspan {
	npages := uintptr(class_to_allocnpages[c.spanclass.sizeclass()]) // 内存页数
	size := uintptr(class_to_size[c.spanclass.sizeclass()])          // 每个对象的大小
	n := (npages << _PageShift) / size                               // 对象数量

	// 从mheap里分配一个span
	s := mheap_.alloc(npages, c.spanclass, false, true)
	if s == nil {
		return nil
	}

	p := s.base()
	s.limit = p + size*n // 设置span的limit指针指向内存区域的末尾

	heapBitsForSpan(s.base()).initSpan(s)
	return s
}
