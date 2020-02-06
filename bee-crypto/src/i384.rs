use byteorder::{
    self,
    ByteOrder,
};

use crate::{
    t243::T243,
    utils::OverflowingAddExt,
    private,
    utils::SplitInteger,
};

use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;

mod constants;

pub use constants::{
    LE_U32_TERNARY_0,
    BE_U8_0,
    BE_U8_1,
    BE_U8_NEG_1,
    BE_U8_MAX,
    BE_U8_MIN,
    BE_U8_2,
    BE_U8_NEG_2,
    BE_U32_0,
    BE_U32_1,
    BE_U32_NEG_1,
    BE_U32_MAX,
    BE_U32_MIN,
    BE_U32_2,
    BE_U32_NEG_2,
    LE_U8_0,
    LE_U8_1,
    LE_U8_NEG_1,
    LE_U8_MAX,
    LE_U8_MIN,
    LE_U8_2,
    LE_U8_NEG_2,
    LE_U32_0,
    LE_U32_1,
    LE_U32_NEG_1,
    LE_U32_MAX,
    LE_U32_MIN,
    LE_U32_2,
    LE_U32_NEG_2,
};

/// The number of bits in an I384
pub const LEN: usize = 384;

/// The number of bytes in an I384
pub const LEN_IN_U8: usize = LEN / 8;
pub const LEN_IN_U32: usize = LEN / 32;

/// The inner representation of a I384 using 48 u8s.
pub type U8Repr = [u8; LEN_IN_U8];

/// The inner representation of a I384 using 12 u32s.
pub type U32Repr = [u32; LEN_IN_U32];

#[derive(Clone, Copy, Debug)]
pub struct BigEndian {}

#[derive(Clone, Copy, Debug)]
pub struct LittleEndian {}

trait EndianType: private::Sealed {}

impl EndianType for BigEndian {}
impl EndianType for LittleEndian {}

pub trait I384Representation: private::Sealed + Clone {
    type T;
    fn iter(&self) -> std::slice::Iter<'_, Self::T>;
}

impl private::Sealed for U8Repr {}
impl private::Sealed for U32Repr {}

impl I384Representation for U8Repr {
    type T = u8;

    fn iter(&self) -> std::slice::Iter<'_, Self::T> {
        (self as &[u8]).iter()
    }
}

impl I384Representation for U32Repr {
    type T = u32;

    fn iter(&self) -> std::slice::Iter<'_, Self::T> {
        (self as &[u32]).iter()
    }
}

/// A biginteger encoding a signed integer with 384 bits.
///
/// `T` is usually taken as a `[u32; 12]` or `[u8; 48]`.
///
/// `E` refers to the endianness of the digits in `T`. This means that in the case of `[u32; 12]`,
/// if `E == BigEndian`, that the u32 at position i=0 is considered the most significant digit. The
/// endianness `E` here makes no statement about the endianness of each single digit within itself
/// (this then is dependent on the endianness of the platform this code is run on).
///
/// For `E == LittleEndian` the digit at the last position is considered to be the most
/// significant.
#[derive(Clone, Copy)]
pub struct I384<E, T> {
    pub(crate) inner: T,
    _phantom: PhantomData<E>,
}

impl<E: fmt::Debug, R: I384Representation, D> fmt::Debug for I384<E, R>
where
    E: fmt::Debug,
    R: I384Representation<T = D>,
    D: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("I384")
            .field("inner", &self.inner.iter())
            .field("_phantom", &self._phantom)
            .finish()
    }
}

macro_rules! impl_const_block_permutations {
    ( $endianness:ty, $repr:ty ) => {
        impl I384<$endianness, $repr> {
            const fn from_array(inner: $repr) -> Self {
                Self {
                    inner,
                    _phantom: PhantomData,
                }
            }
        }
    };

    ( { $endianness:ty }, { $repr:ty } ) => {
        impl_const_block_permutations!($endianness, $repr)
    };

    ( { $endianness:ty }, { $( $repr:ty ),+ $(,)? } ) => {

        $(
            impl_const_block_permutations!($endianness, $repr);
        )+
    };

    ( { $endianness:ty, $( $rest:ty ),+ }, { $( $repr:ty ),+ $(,)? } ) => {

        impl_const_block_permutations!( { $endianness }, { $( $repr ),+ });

        impl_const_block_permutations!( { $( $rest ),+ }, { $( $repr ),+ });
    };
}

impl_const_block_permutations!( { BigEndian, LittleEndian }, { U8Repr, U32Repr });

macro_rules! impl_constants {
    ( $( $t:ty => [ $zero:expr, $one:expr, $neg_one:expr, $two:expr, $neg_two:expr, $max:expr, $min:expr]),+ $(,)? ) => {
        $(
            impl $t {
                pub const fn zero() -> Self {
                    $zero
                }

                pub const fn one() -> Self {
                    $one
                }

                pub const fn neg_one() -> Self {
                    $neg_one
                }

                pub const fn two() -> Self {
                    $two
                }

                pub const fn neg_two() -> Self {
                    $neg_two
                }

                pub const fn max() -> Self {
                    $max
                }

                pub const fn min() -> Self {
                    $min
                }
            }
        )+
    };
}

impl_constants!(
    I384<BigEndian, U8Repr> => [
    BE_U8_0,
    BE_U8_1,
    BE_U8_NEG_1,
    BE_U8_2,
    BE_U8_NEG_2,
    BE_U8_MAX,
    BE_U8_MIN
    ],
    I384<LittleEndian, U8Repr> => [
    LE_U8_0,
    LE_U8_1,
    LE_U8_NEG_1,
    LE_U8_2,
    LE_U8_NEG_2,
    LE_U8_MAX,
    LE_U8_MIN
    ],
    I384<BigEndian, U32Repr> => [
    BE_U32_0,
    BE_U32_1,
    BE_U32_NEG_1,
    BE_U32_2,
    BE_U32_NEG_2,
    BE_U32_MAX,
    BE_U32_MIN
    ],
    I384<LittleEndian, U32Repr> => [
    LE_U32_0,
    LE_U32_1,
    LE_U32_NEG_1,
    LE_U32_2,
    LE_U32_NEG_2,
    LE_U32_MAX,
    LE_U32_MIN
    ],
);

impl I384<LittleEndian, U32Repr> {
    /// Adds `other` onto `self` in place.
    pub(crate) fn add_inplace(&mut self, other: Self) {
        let mut overflown = false;
        let self_iter = self.inner.iter_mut();
        let other_iter = other.inner.iter();

        for (s, o) in self_iter.zip(other_iter) {
            let (sum, still_overflown) = s.overflowing_add_with_carry(*o, overflown as u32);
            *s = sum;
            overflown = still_overflown;
        }
    }

    /// Adds `other` in place, returning the number of digits required accomodate `other` (starting
    /// from the least significant one).
    pub(crate) fn add_integer_inplace<T: Into<u32>>(&mut self, other: T) -> usize {
        let other = other.into();

        let (sum, mut overflown) = self.inner[0].overflowing_add(other);
        self.inner[0] = sum;

        let mut i = 1;

        while overflown {
            let (sum, still_overflown) = self.inner[i].overflowing_add(1u32);
            self.inner[i] = sum;
            overflown = still_overflown;
            i += 1;
        }

        i
    }

    pub(crate) fn is_positive(&self) -> bool {
        (self.inner[LEN_IN_U32-1] & 0x7000_0000) == 0x7000_0000
    }

    pub(crate) fn is_negative(&self) -> bool {
        !self.is_positive()
    }

    /// Applies logical not to all elements in a `&[u32]`, modfiying them in place.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let xs: I384<LittleEndian, _> = I384::from_array([0xffff_ffffu32; LEN_IN_U32]);
    /// let mut ys = I384::from_array([0x0000_0000u32; LEN_IN_U32]);
    /// ys.not_inplace();
    /// assert_eq!(xs, ys);
    /// ```
    fn not_inplace(&mut self) {
        for i in self.inner.iter_mut() {
            *i = !*i;
        }
    }

    /// Subtract `other` from `self` inplace.
    ///
    /// This function is defined in terms of `overflowing_add` by making use of the following identity
    /// (in terms of Two's complement, and where `!` is logical bitwise negation):
    ///
    /// !x = -x -1 => -x = !x + 1
    ///
    /// TODO: Verifiy that the final assert is indeed not necessary. Preliminary testing shows that
    /// results are as expected.
    pub(crate) fn sub_inplace(&mut self, other: Self) {
        let self_iter = self.inner.iter_mut();
        let other_iter = other.inner.iter();

        // The first `borrow` is always true because the addition operation needs to account for the
        // above).
        let mut borrow = true;

        for (s, o) in self_iter.zip(other_iter) {
            let (sum, has_overflown) = s.overflowing_add_with_carry(!*o, borrow as u32);
            *s = sum;
            borrow = has_overflown;
        }

        // TODO: Is this truly necessary?
        // assert!(borrow);
    }

    /// Subtracts `other` in place, returning the number of digits required accomodate `other`
    /// (starting from the least significant one).
    fn sub_integer_inplace<T: Into<u32>>(&mut self, other: T) -> usize {
        let other = other.into();

        let (sum, mut overflown) = self.inner[0].overflowing_sub(other);
        self.inner[0] = sum;

        let mut i = 1;

        while overflown {
            let (sum, still_overflown) = self.inner[i].overflowing_sub(1u32);
            self.inner[i] = sum;
            overflown = still_overflown;
            i += 1;
        }
        i
    }
}

impl Eq for I384<BigEndian, U8Repr> {}

impl PartialEq for I384<BigEndian, U8Repr> {
    fn eq(&self, other: &Self) -> bool {
        let mut are_equal = true;
        for (a, b) in self.inner.iter().zip(other.inner.iter()) {
            are_equal &= a == b
        }
        are_equal
    }
}

impl PartialOrd for I384<BigEndian, U8Repr> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;

        let self_iter = self.inner.iter();
        let other_iter = other.inner.iter();

        let mut zipped_iter = self_iter.zip(other_iter);

        // The most significant u8 (MSU8) has to be handled separately.
        //
        // If the most significant bit of both numbers is set, then the comparison operators
        // have to be reversed.
        //
        // Note that this is only relevant to the comparison operators between the less significant
        // u8 if the two MSU8s are equal. If they are not equal, then an early return will be
        // triggered.

        const UMAX: u8 = std::u8::MAX;
        let numbers_negative = match zipped_iter.next() {
            // Case 1: both numbers are negative, s is less
            Some(( s @ 0x70..=UMAX, o @ 0x70..=UMAX )) if s > o => return Some(Less),

            // Case 2: both numbers are negative, s is greater
            Some(( s @ 0x70..=UMAX, o @ 0x70..=UMAX )) if s < o => return Some(Greater),

            // Case 3: both numbers are negative, but equal
            Some(( 0x70..=UMAX, 0x70..=UMAX )) => true,

            // Case 4: only s is negative
            Some(( 0x70..=UMAX, _ )) => return Some(Less),

            // Case 5: only o is negative
            Some(( _, 0x70..=UMAX )) => return Some(Greater),

            // Case 6: both are positive
            Some((s, o)) if s > o => return Some(Greater),

            Some((s, o)) if s < o => return Some(Less),

            // Fallthrough case; only happens if s == o
            Some(_) => false,

            // The array inside `I384` always has a length larger zero, so the first element is
            // guaranteed to exist.
            None => unreachable!(),
        };

        // Create two separate loops as to avoid repeatedly checking `numbers_negative`.
        if numbers_negative {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Less)
                } else if s < o {
                    return Some(Greater)
                }
            }
        } else {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Greater)
                } else if s < o {
                    return Some(Less)
                }
            }
        }

        Some(Equal)
    }
}

impl Ord for I384<BigEndian, U8Repr> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,

            // The ordering is total, hence `partial_cmp` will never return `None`.
            None => unreachable!(),
        }
    }
}

impl Eq for I384<BigEndian, U32Repr> {}

impl PartialEq for I384<BigEndian, U32Repr> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl PartialOrd for I384<BigEndian, U32Repr> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;

        let self_iter = self.inner.iter();
        let other_iter = other.inner.iter();

        let mut zipped_iter = self_iter.zip(other_iter);

        // The most significant u32 (MSU32) has to be handled separately.
        //
        // If the most significant bit of both numbers is set, then the comparison operators
        // have to be reversed.
        //
        // Note that this is only relevant to the comparison operators between the less significant
        // u32 if the two MSU32s are equal. If they are not equal, then an early return will be
        // triggered.

        const UMAX: u32 = std::u32::MAX;
        let numbers_negative = match zipped_iter.next() {
            // Case 1: both numbers are negative, s is less
            Some(( s @ 0x7000_0000..=UMAX, o @ 0x7000_0000..=UMAX )) if s > o => return Some(Less),

            // Case 2: both numbers are negative, s is greater
            Some(( s @ 0x7000_0000..=UMAX, o @ 0x7000_0000..=UMAX )) if s < o => return Some(Greater),

            // Case 3: both numbers are negative, but equal
            Some(( 0x7000_0000..=UMAX, 0x7000_0000..=UMAX )) => true,

            // Case 4: only s is negative
            Some(( 0x7000_0000..=UMAX, _ )) => return Some(Less),

            // Case 5: only o is negative
            Some(( _, 0x7000_0000..=UMAX )) => return Some(Greater),

            // Case 6: both are positive
            Some((s, o)) if s > o => return Some(Greater),

            Some((s, o)) if s < o => return Some(Less),

            // Fallthrough case; only happens if s == o
            Some(_) => false,

            // The array inside `I384` always has a length larger zero, so the first element is
            // guaranteed to exist.
            None => unreachable!(),
        };

        // Create two separate loops as to avoid repeatedly checking `numbers_negative`.
        if numbers_negative {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Less)
                } else if s < o {
                    return Some(Greater)
                }
            }
        } else {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Greater)
                } else if s < o {
                    return Some(Less)
                }
            }
        }

        Some(Equal)
    }
}

impl Ord for I384<BigEndian, U32Repr> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,

            // The ordering is total, hence `partial_cmp` will never return `None`.
            None => unreachable!(),
        }
    }
}

impl Eq for I384<LittleEndian, U8Repr> {}

impl PartialEq for I384<LittleEndian, U8Repr> {
    fn eq(&self, other: &Self) -> bool {
        let mut are_equal = true;
        for (a, b) in self.inner.iter().zip(other.inner.iter()) {
            are_equal &= a == b
        }
        are_equal
    }
}

impl PartialOrd for I384<LittleEndian, U8Repr> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;

        let self_iter = self.inner.iter().rev();
        let other_iter = other.inner.iter().rev();

        let mut zipped_iter = self_iter.zip(other_iter);

        // The most significant u8 (MSU8) has to be handled separately.
        //
        // If the most significant bit of both numbers is set, then the comparison operators
        // have to be reversed.
        //
        // Note that this is only relevant to the comparison operators between the less significant
        // u8 if the two MSU8s are equal. If they are not equal, then an early return will be
        // triggered.

        const UMAX: u8 = std::u8::MAX;
        let numbers_negative = match zipped_iter.next() {
            // Case 1: both numbers are negative, s is less
            Some(( s @ 0x70..=UMAX, o @ 0x70..=UMAX )) if s > o => return Some(Less),

            // Case 2: both numbers are negative, s is greater
            Some(( s @ 0x70..=UMAX, o @ 0x70..=UMAX )) if s < o => return Some(Greater),

            // Case 3: both numbers are negative, but equal
            Some(( 0x70..=UMAX, 0x70..=UMAX )) => true,

            // Case 4: only s is negative
            Some(( 0x70..=UMAX, _ )) => return Some(Less),

            // Case 5: only o is negative
            Some(( _, 0x70..=UMAX )) => return Some(Greater),

            // Case 6: both are positive
            Some((s, o)) if s > o => return Some(Greater),

            Some((s, o)) if s < o => return Some(Less),

            // Fallthrough case; only happens if s == o
            Some(_) => false,

            // The array inside `I384` always has a length larger zero, so the first element is
            // guaranteed to exist.
            None => unreachable!(),
        };

        // Create two separate loops as to avoid repeatedly checking `numbers_negative`.
        if numbers_negative {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Less)
                } else if s < o {
                    return Some(Greater)
                }
            }
        } else {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Greater)
                } else if s < o {
                    return Some(Less)
                }
            }
        }

        Some(Equal)
    }
}

impl Ord for I384<LittleEndian, U8Repr> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,

            // The ordering is total, hence `partial_cmp` will never return `None`.
            None => unreachable!(),
        }
    }
}

impl Eq for I384<LittleEndian, U32Repr> {}

impl PartialEq for I384<LittleEndian, U32Repr> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl PartialOrd for I384<LittleEndian, U32Repr> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;

        let self_iter = self.inner.iter().rev();
        let other_iter = other.inner.iter().rev();

        let mut zipped_iter = self_iter.zip(other_iter);

        // The most significant u32 (MSU32) has to be handled separately.
        //
        // If the most significant bit of both numbers is set, then the comparison operators
        // have to be reversed.
        //
        // Note that this is only relevant to the comparison operators between the less significant
        // u32 if the two MSU32s are equal. If they are not equal, then an early return will be
        // triggered.

        const UMAX: u32 = std::u32::MAX;
        let numbers_negative = match zipped_iter.next() {
            // Case 1: both numbers are negative, s is less
            Some(( s @ 0x7000_0000..=UMAX, o @ 0x7000_0000..=UMAX )) if s > o => return Some(Less),

            // Case 2: both numbers are negative, s is greater
            Some(( s @ 0x7000_0000..=UMAX, o @ 0x7000_0000..=UMAX )) if s < o => return Some(Greater),

            // Case 3: both numbers are negative, but equal
            Some(( 0x7000_0000..=UMAX, 0x7000_0000..=UMAX )) => true,

            // Case 4: only s is negative
            Some(( 0x7000_0000..=UMAX, _ )) => return Some(Less),

            // Case 5: only o is negative
            Some(( _, 0x7000_0000..=UMAX )) => return Some(Greater),

            // Case 6: both are positive
            Some((s, o)) if s > o => return Some(Greater),

            Some((s, o)) if s < o => return Some(Less),

            // Fallthrough case; only happens if s == o
            Some(_) => false,

            // The array inside `I384` always has a length larger zero, so the first element is
            // guaranteed to exist.
            None => unreachable!(),
        };

        // Create two separate loops as to avoid repeatedly checking `numbers_negative`.
        if numbers_negative {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Less)
                } else if s < o {
                    return Some(Greater)
                }
            }
        } else {
            for (s, o) in zipped_iter {
                if s > o {
                    return Some(Greater)
                } else if s < o {
                    return Some(Less)
                }
            }
        }

        Some(Equal)
    }
}

impl Ord for I384<LittleEndian, U32Repr> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,

            // The ordering is total, hence `partial_cmp` will never return `None`.
            None => unreachable!(),
        }
    }
}

impl From<T243> for I384<BigEndian, U32Repr> {
    /// Converts a signed integer represented by the balanced trits in `t243` to the signed binary
    /// integer `i384`. `t243` is assumed to be in little endian representation, with the most
    /// significant trit being at the largest index in the array.
    ///
    /// This is done in the following steps:
    ///
    /// 1. `1` is added to all balanced trits, making them *unsigned*: `{-1, 0, 1} -> {0, 1, 2}`.
    /// 2. The `t243` are converted to base 10 and through this immediately to `i384` by calculating the sum `s`:
    ///
    /// ```ignore
    /// s = t_242 * 3^241 + t_241 * 3^240 + ...
    ///   + t_{i+1} * 3^{i} + t_i * 3^{i-1} + t_{i-1} * 3^{i-2} + ...
    ///   + t_1 * 3 + t_0
    /// ```
    ///
    /// To perform this sum efficiently, its accumulation is staggered, so that each multiplication
    /// by 3 is done in each iteration of accumulating loop. This can be understood by factoring
    /// the powers of 3 from the previous sum:
    ///
    /// ```ignore
    /// s = (...((t_242 * 3 + t_241) * 3 + t_240) * 3 + ...
    ///   +  ...((t_{i+1} * 3 + t_i) * 3 + t_{i-1}) * 3 + ...
    ///   +  ...t_1) * 3 + t_0  
    /// ```
    ///
    /// Or in procedural form, with the sum being accumulated in `acc` and with the index `i`
    /// running from `[242..0`]:
    ///
    /// ```ignore
    /// acc = 0
    /// for i, trit in trits.rev():
    ///     acc := acc + trit * 3^i
    /// ```
    fn from(value: T243) -> Self {
        let i384_le: I384<LittleEndian, U32Repr> = value.into();
        i384_le.into()
    }
}

impl From<T243> for I384<LittleEndian, U32Repr> {
    /// Converts a signed integer represented by the balanced trits in `t243` to the signed binary
    /// integer `i384`. `t243` is assumed to be in little endian representation, with the most
    /// significant trit being at the largest index in the array.
    ///
    /// This is done in the following steps:
    ///
    /// 1. `1` is added to all balanced trits, making them *unsigned*: `{-1, 0, 1} -> {0, 1, 2}`.
    /// 2. The `t243` are converted to base 10 and through this immediately to `i384` by calculating the sum `s`:
    ///
    /// ```ignore
    /// s = t_242 * 3^241 + t_241 * 3^240 + ...
    ///   + t_{i+1} * 3^{i} + t_i * 3^{i-1} + t_{i-1} * 3^{i-2} + ...
    ///   + t_1 * 3 + t_0
    /// ```
    ///
    /// To perform this sum efficiently, its accumulation is staggered, so that each multiplication
    /// by 3 is done in each iteration of accumulating loop. This can be understood by factoring
    /// the powers of 3 from the previous sum:
    ///
    /// ```ignore
    /// s = (...((t_242 * 3 + t_241) * 3 + t_240) * 3 + ...
    ///   +  ...((t_{i+1} * 3 + t_i) * 3 + t_{i-1}) * 3 + ...
    ///   +  ...t_1) * 3 + t_0  
    /// ```
    ///
    /// Or in procedural form, with the sum being accumulated in `acc` and with the index `i`
    /// running from `[242..0`]:
    ///
    /// ```ignore
    /// acc = 0
    /// for i, trit in trits.rev():
    ///     acc := acc + trit * 3^i
    /// ```
    fn from(value: T243) -> Self {
        // This is the `Vec<i8>` inside `TritsBuf`
        let mut raw_trits_buf = value.into_inner().into_inner();

        // Shift the balanced trits from {-1, 0, 1} to {0, 1, 2}
        for element in raw_trits_buf.iter_mut() {
            *element += 1;
        }

        // The accumulator is a little endian bigint using `u32` as an internal representation
        let mut accumulator = I384::<LittleEndian, U32Repr>::zero();
        let mut accumulator_extent = 1;

        // Iterate over all trits starting from the most significant one.
        for raw_trit in raw_trits_buf.iter().rev() {

            // Iterate over all digits in the bigint accumulator, multiplying by 3 into a `u64`.
            // Overflow is handled by taking the lower `u32` as the new digit, and the higher `u32`
            // as the carry.
            let mut carry: u32 = 0;
            for digit in accumulator.inner[0..accumulator_extent].iter_mut() {
                let new_digit = *digit as u64 * 3u64 + carry as u64;

                *digit = new_digit.lo();
                carry = new_digit.hi();
            }

            if carry != 0 {
                unsafe {
                    *accumulator.inner.get_unchecked_mut(accumulator_extent) = carry;
                }
                accumulator_extent += 1;
            }

            let new_extent = accumulator.add_integer_inplace(*raw_trit as u32);
            if new_extent > accumulator_extent {
                accumulator_extent = new_extent;
            }
        }

        // Shift the bigint into the `signed` range by subtracting `LE_U32_TERNARY_0` from it. `LE_U32_TERNARY_0`
        // is the resulting (unsigned) biginteger obtained by converting the (unsigned/unbalanced)
        // `t243` consisting entirely of `1`, i.e. `t243 = [1, 1, ..., 1]` (or zero in the case of
        // balanced ternary).
        //
        //
        // NOTE: Below is the old implementation obtained by converting the legacy C code. It was
        // implemented the way it reads there because it was assumed that there was no wrapping
        // subtraction. However, it seems like subtraction works just fine, testing various edge
        // cases, see the bottom `tests` module of this page.
        //
        // use Ordering::*;
        // match accumulator.cmp(&LE_U32_TERNARY_0) {

        //     // Case 1: performing the subtraction would not cause an underflow
        //     Greater => accumulator.sub_inplace(LE_U32_TERNARY_0),

        //     // Case 2: perfoming the subtraction would cause an underflow
        //     Less => {
        //         // Simulate a wrapping sub.
        //         let mut tmp = LE_U32_TERNARY_0;
        //         tmp.sub_inplace(accumulator);
        //         tmp.not_inplace();
        //         tmp.add_integer_inplace(1u32);
        //         accumulator = tmp;
        //     }

        //     // Case 3: 
        //     Equal => {
        //         accumulator.clone_from(&LE_U32_TERNARY_0);
        //         accumulator.not_inplace();
        //         accumulator.add_integer_inplace(1u32);
        //     }
        // }

        accumulator.sub_inplace(LE_U32_TERNARY_0);
        accumulator
    }
}

impl From<I384<BigEndian, U32Repr>> for I384<BigEndian, U8Repr> {
    fn from(value: I384<BigEndian, U32Repr>) -> Self {
        let mut i384_u8 = Self::zero();
        byteorder::BigEndian::write_u32_into(&value.inner, &mut i384_u8.inner);
        i384_u8
    }
}

impl From<I384<BigEndian, U8Repr>> for I384<BigEndian, U32Repr> {
    fn from(value: I384<BigEndian, U8Repr>) -> Self {
        let mut i384_u32 = Self::zero();
        byteorder::BigEndian::read_u32_into(&value.inner, &mut i384_u32.inner);
        i384_u32
    }
}

impl From<I384<LittleEndian, U32Repr>> for I384<LittleEndian, U8Repr> {
    fn from(value: I384<LittleEndian, U32Repr>) -> Self {
        let mut i384_u8 = Self::zero();
        byteorder::LittleEndian::write_u32_into(&value.inner, &mut i384_u8.inner);
        i384_u8
    }
}

impl From<I384<LittleEndian, U8Repr>> for I384<LittleEndian, U32Repr> {
    fn from(value: I384<LittleEndian, U8Repr>) -> Self {
        let mut i384_u32 = I384::<LittleEndian, U32Repr>::zero();
        byteorder::LittleEndian::read_u32_into(&value.inner, &mut i384_u32.inner);
        i384_u32
    }
}

macro_rules! impl_toggle_endianness {
    ($t:ty, $src_endian:ty, $dst_endian:ty) => {
        impl From<I384<$src_endian, $t>> for I384<$dst_endian, $t> {
            fn from(value: I384<$src_endian, $t>) -> Self {
                let mut inner = value.inner;
                inner.reverse();
                Self {
                    inner,
                    _phantom: PhantomData,
                }
            }
        }
    }
}

macro_rules! impl_all_toggle_endianness {
    ( $( $t:ty ),* ) => {
        $(
            impl_toggle_endianness!($t, LittleEndian, BigEndian);
            impl_toggle_endianness!($t, BigEndian, LittleEndian);
        )*
    }
}

impl_all_toggle_endianness!(U8Repr, U32Repr);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_binary_op {
        ( $( [$testname:ident, $binop:ident, $fst:ident, $snd:ident, $res:ident] ),+ $(,)? ) => {
            mod little_endian_binary_op {
                use super::*;

                $(
                    #[test]
                    fn $testname() {
                        let mut fst = $fst;
                        fst.$binop($snd);
                        assert_eq!(fst, $res);
                    }
                )+
            }

        }
    }

    test_binary_op!(
        [one_minus_neg_one_is_two, sub_inplace, LE_U32_1, LE_U32_NEG_1, LE_U32_2],
        [one_minus_one_is_zero, sub_inplace, LE_U32_1, LE_U32_1, LE_U32_0],
        [one_plus_one_is_two, add_inplace, LE_U32_1, LE_U32_1, LE_U32_2],
        [one_plus_neg_one_is_zero, add_inplace, LE_U32_1, LE_U32_NEG_1, LE_U32_0],
        [neg_one_minus_one_is_neg_two, sub_inplace, LE_U32_NEG_1, LE_U32_1, LE_U32_NEG_2],
        [neg_one_minus_neg_one_is_zero, sub_inplace, LE_U32_NEG_1, LE_U32_NEG_1, LE_U32_0],
        [neg_one_plus_one_is_zero, add_inplace, LE_U32_NEG_1, LE_U32_1, LE_U32_0],
        [neg_one_plus_neg_one_is_neg_two, add_inplace, LE_U32_NEG_1, LE_U32_NEG_1, LE_U32_NEG_2],
        [min_minus_one_is_max, sub_inplace, LE_U32_MIN, LE_U32_1, LE_U32_MAX],
        [min_plus_neg_one_is_max, add_inplace, LE_U32_MIN, LE_U32_NEG_1, LE_U32_MAX],
        [max_plus_one_is_min, add_inplace, LE_U32_MAX, LE_U32_1, LE_U32_MIN],
        [max_minus_neg_one_is_min, sub_inplace, LE_U32_MAX, LE_U32_NEG_1, LE_U32_MIN],
        [zero_minus_one_is_neg_one, sub_inplace, LE_U32_0, LE_U32_1, LE_U32_NEG_1],
        [zero_minus_neg_one_is_one, sub_inplace, LE_U32_0, LE_U32_NEG_1, LE_U32_1],
        [zero_plus_one_is_one, add_inplace, LE_U32_0, LE_U32_1, LE_U32_1],
        [zero_plus_neg_one_is_neg_one, add_inplace, LE_U32_0, LE_U32_NEG_1, LE_U32_NEG_1],
    );

    macro_rules! endianness_test_function {
        ( $testname:ident, $repr:ty, $src_endian:ty, $dst_endian:ty, $val_fn:ident) => {
            #[test]
            fn $testname() {
                let original = I384::<$src_endian, $repr>::$val_fn();
                let target = I384::<$dst_endian, $repr>::$val_fn();
                let converted = Into::<I384<$dst_endian, $repr>>::into(original);
                assert_eq!(converted, target);
            }
        }
    }

    macro_rules! test_endianness_toggle {

        ($modname:ident, $repr:ty, $src_endian:ty, $dst_endian:ty) => {
            mod $modname {
                use super::*;
                endianness_test_function!(zero_is_zero, $repr, $src_endian, $dst_endian, zero);
                endianness_test_function!(one_is_one, $repr, $src_endian, $dst_endian, one);
                endianness_test_function!(neg_one_is_neg_one, $repr, $src_endian, $dst_endian, neg_one);
                endianness_test_function!(two_is_two, $repr, $src_endian, $dst_endian, two);
                endianness_test_function!(neg_two_is_neg_two, $repr, $src_endian, $dst_endian, neg_two);
                endianness_test_function!(max_is_max, $repr, $src_endian, $dst_endian, max);
                endianness_test_function!(min_is_min, $repr, $src_endian, $dst_endian, min);
            }
        };

        ( $( [ $modname:ident, $repr:ty ] ),+ $(,)? ) => {

            mod toggle_endianness {
                use crate::i384::{
                    I384,
                    BigEndian,
                    LittleEndian,
                    U8Repr,
                    U32Repr,
                };
                $(
                    mod $modname {
                        use super::*;
                        test_endianness_toggle!(big_to_little, $repr, BigEndian, LittleEndian);
                        test_endianness_toggle!(little_to_big, $repr, LittleEndian, BigEndian);
                    }
                )+
            }
        }

    }

    test_endianness_toggle!(
        [u8_repr, U8Repr],
        [u32_repr, U32Repr],
    );

    macro_rules! endianness_roundtrip_test_function {
        ( $testname:ident, $repr:ty, $src_endian:ty, $dst_endian:ty, $val_fn:ident ) => {
            #[test]
            fn $testname() {
                let original = I384::<$src_endian, $repr>::$val_fn();
                let converted = Into::<I384<$dst_endian, $repr>>::into(original);
                let roundtripped = Into::<I384<$src_endian, $repr>>::into(converted);
                assert_eq!(roundtripped, original);
            }
        }
    }

    macro_rules! test_endianness_roundtrip {
        ( $modname:ident, $repr:ty, $src_endian:ty, $dst_endian:ty) => {
            mod $modname {
                use super::*;
                endianness_roundtrip_test_function!(zero_is_zero, $repr, $src_endian, $dst_endian, zero);
                endianness_roundtrip_test_function!(one_is_one, $repr, $src_endian, $dst_endian, one);
                endianness_roundtrip_test_function!(neg_one_is_neg_one, $repr, $src_endian, $dst_endian, neg_one);
                endianness_roundtrip_test_function!(two_is_two, $repr, $src_endian, $dst_endian, two);
                endianness_roundtrip_test_function!(neg_two_is_neg_two, $repr, $src_endian, $dst_endian, neg_two);
                endianness_roundtrip_test_function!(max_is_max, $repr, $src_endian, $dst_endian, max);
                endianness_roundtrip_test_function!(min_is_min, $repr, $src_endian, $dst_endian, min);
            }
        }
    }

    macro_rules! endianness_roundtrip {
        ( $( [ $modname:ident, $repr:ty ] ),+ $(,)? ) => {

            mod endianness_roundtrip {
                use crate::i384::{
                    I384,
                    BigEndian,
                    LittleEndian,
                    U8Repr,
                    U32Repr,
                };
                $(
                    mod $modname {
                        use super::*;
                        test_endianness_roundtrip!(big, $repr, BigEndian, LittleEndian);
                        test_endianness_roundtrip!(little, $repr, LittleEndian, BigEndian);
                    }
                )+
            }
        };
    }

    endianness_roundtrip!(
        [u8_repr, U8Repr],
        [u32_repr, U32Repr],
    );

    macro_rules! repr_roundtrip_test_function {
        ( $testname:ident, $endianness:ty, $src_repr:ty, $dst_repr:ty, $val_fn:ident ) => {
            #[test]
            fn $testname() {
                let original = I384::<$endianness, $src_repr>::$val_fn();
                let converted = Into::<I384<$endianness, $dst_repr>>::into(original);
                let roundtripped = Into::<I384<$endianness, $src_repr>>::into(converted);
                assert_eq!(roundtripped, original);
            }
        }
    }

    macro_rules! test_repr_roundtrip {
        ( $modname:ident, $endianness:ty, $src_repr:ty, $dst_repr:ty ) => {
            mod $modname {
                use super::*;
                repr_roundtrip_test_function!(zero_is_zero, $endianness, $src_repr, $dst_repr, zero);
                repr_roundtrip_test_function!(one_is_one, $endianness, $src_repr, $dst_repr, one);
                repr_roundtrip_test_function!(neg_one_is_neg_one, $endianness, $src_repr, $dst_repr, neg_one);
                repr_roundtrip_test_function!(two_is_two, $endianness, $src_repr, $dst_repr, two);
                repr_roundtrip_test_function!(neg_two_is_neg_two, $endianness, $src_repr, $dst_repr, neg_two);
                repr_roundtrip_test_function!(max_is_max, $endianness, $src_repr, $dst_repr, max);
                repr_roundtrip_test_function!(min_is_min, $endianness, $src_repr, $dst_repr, min);
            }
        }
    }

    macro_rules! repr_roundtrip {
        ( $( [ $modname:ident, $endianness:ty ] ),+ $(,)? ) => {
            mod repr_roundtrip {
                use crate::i384::{
                    I384,
                    BigEndian,
                    LittleEndian,
                    U8Repr,
                    U32Repr,
                };
                $(
                    mod $modname {
                        use super::*;
                        test_repr_roundtrip!(u8_repr, $endianness, U8Repr, U32Repr);
                        test_repr_roundtrip!(u32_repr, $endianness, U32Repr, U8Repr);
                    }
                )+
            }
        };
    }

    repr_roundtrip!(
        [big_endian, BigEndian],
        [little_endian, LittleEndian],
    );
}
