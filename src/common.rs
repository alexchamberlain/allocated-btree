use core::mem::MaybeUninit;
use core::ptr;
use generic_array::sequence::GenericSequence;

use generic_array::GenericArray;

pub trait InsertExt<V> {
    fn insert(&mut self, idx: usize, len: usize, value: V);
}

impl<V, B: generic_array::ArrayLength> InsertExt<V> for GenericArray<V, B> {
    fn insert(&mut self, idx: usize, len: usize, value: V) {
        assert!(len <= B::to_usize());
        // SAFETY: We shift elements from idx to idx+len-1 one position to the right.
        // The assertion ensures len <= capacity, and idx <= len is implied by usage.
        // The regions [idx..len) and [idx+1..len+1) may overlap, so ptr::copy is correct.
        // SAFETY: idx is within bounds (idx <= len <= capacity)
        let src = unsafe { self.as_mut_ptr().add(idx) };
        // SAFETY: idx + 1 <= len + 1 <= capacity + 1, which is valid for pointer arithmetic
        let dst = unsafe { self.as_mut_ptr().add(idx + 1) };
        // SAFETY: src and dst are valid pointers within the array, and ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, len - idx);
        }
        // SAFETY: After the shift, self[idx] is uninitialized. We write a valid value to it.
        unsafe {
            ptr::write(&mut self[idx], value);
        }
    }
}

impl<V, B: generic_array::ArrayLength> InsertExt<V> for GenericArray<MaybeUninit<V>, B> {
    fn insert(&mut self, idx: usize, len: usize, value: V) {
        assert!(len <= B::to_usize());
        // SAFETY: We shift MaybeUninit elements from idx to idx+len-1 one position right.
        // MaybeUninit<V> can be safely copied regardless of initialization state.
        // The assertion ensures len <= capacity.
        // SAFETY: idx is within bounds (idx <= len <= capacity)
        let src = unsafe { self.as_mut_ptr().add(idx) };
        // SAFETY: idx + 1 <= len + 1 <= capacity + 1, which is valid for pointer arithmetic
        let dst = unsafe { self.as_mut_ptr().add(idx + 1) };
        // SAFETY: src and dst are valid pointers within the array, and ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, len - idx);
        }
        self[idx].write(value);
    }
}

pub trait TakeInsertExt<V, W> {
    fn pop_at(&mut self, idx: usize, len: usize) -> V;
    fn take(other: &mut [W]) -> Self;
    fn take_and_insert(other: &mut [W], idx: usize, len: usize, value: V) -> Self;
}

impl<V, B: generic_array::ArrayLength> TakeInsertExt<V, MaybeUninit<V>>
    for GenericArray<MaybeUninit<V>, B>
{
    fn pop_at(&mut self, idx: usize, len: usize) -> V {
        assert!(len <= B::to_usize());
        // SAFETY: Caller ensures self[idx] is initialized. We read and take ownership.
        let value = unsafe { self[idx].assume_init_read() };
        // SAFETY: Shift elements left to fill the gap at idx.
        // Elements [idx+1..len) are moved to [idx..len-1).
        // SAFETY: idx + 1 <= len <= capacity, so this offset is within bounds
        let src = unsafe { self.as_mut_ptr().add(idx + 1) };
        // SAFETY: idx < len (implied by idx + 1 <= len), so idx is within bounds
        let dst = unsafe { self.as_mut_ptr().add(idx) };
        // SAFETY: src and dst are valid pointers within the array, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, len - idx - 1);
        }

        value
    }

    fn take(other: &mut [MaybeUninit<V>]) -> Self {
        assert!(other.len() <= B::to_usize());
        let mut new_values = GenericArray::uninit();
        // SAFETY: Copy MaybeUninit<V> elements from other to new_values.
        // MaybeUninit<V> is always safe to copy.
        unsafe {
            ptr::copy(other.as_ptr(), new_values.as_mut_ptr(), other.len());
        }
        new_values
    }

    fn take_and_insert(other: &mut [MaybeUninit<V>], idx: usize, len: usize, value: V) -> Self {
        assert!(len <= B::to_usize());
        assert!(idx <= len);

        let mut new_values = GenericArray::uninit();
        // SAFETY: Copy first `idx` elements from other to new_values.
        // idx <= len <= capacity, so copying idx elements is within bounds.
        unsafe {
            ptr::copy(other.as_ptr(), new_values.as_mut_ptr(), idx);
        }
        // SAFETY: Write the new value at position idx.
        // idx <= len < capacity, so idx is a valid position in new_values.
        unsafe {
            ptr::write(new_values[idx].as_mut_ptr(), value);
        }
        // SAFETY: Copy remainder elements after idx.
        // SAFETY: idx < other.len() (since idx <= len and len > 0 for non-empty insert)
        let src = unsafe { other.as_ptr().add(idx) };
        // SAFETY: idx + 1 <= len + 1 <= capacity, which is valid for new_values
        let dst = unsafe { new_values.as_mut_ptr().add(idx + 1) };
        // SAFETY: src and dst point to non-overlapping valid memory regions
        unsafe {
            ptr::copy(src, dst, len - idx);
        }
        new_values
    }
}

impl<V, B: generic_array::ArrayLength> TakeInsertExt<Option<V>, Option<V>>
    for GenericArray<Option<V>, B>
{
    fn pop_at(&mut self, idx: usize, len: usize) -> Option<V> {
        assert!(len <= B::to_usize());
        let value = self[idx].take();
        // SAFETY: Shift Option<V> elements left to fill the gap at idx.
        // Elements [idx+1..len) are moved to [idx..len-1).
        // Option<V> is Copy when V is not, so ptr::copy is safe.
        // SAFETY: idx + 1 <= len <= capacity, so this offset is within bounds
        let src = unsafe { self.as_ptr().add(idx + 1) };
        // SAFETY: idx < len (implied by removing at idx), so idx is within bounds
        let dst = unsafe { self.as_mut_ptr().add(idx) };
        // SAFETY: src and dst are valid pointers within the array, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, len - idx - 1);
        }
        value
    }

    fn take(other: &mut [Option<V>]) -> Self {
        assert!(other.len() <= B::to_usize());

        GenericArray::generate(|i| {
            if i < other.len() {
                other[i].take()
            } else {
                None
            }
        })
    }

    fn take_and_insert(
        other: &mut [Option<V>],
        idx: usize,
        len: usize,
        mut value: Option<V>,
    ) -> Self {
        assert!(len <= B::to_usize());
        assert!(idx <= len);

        GenericArray::generate(|j| {
            if j < idx {
                other[j].take()
            } else if j == idx {
                value.take()
            } else if j - 1 < other.len() {
                other[j - 1].take()
            } else {
                None
            }
        })
    }
}
