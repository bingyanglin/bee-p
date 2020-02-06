//! This module contains logic to convert an integer encoded by 243 trits to the same
//! integer encoded by 384 bits (or 48 signed bytes, `i8`).
//!
//! At the core of this a slice of binary-coded, balanced trits is interpreted
//! fanned-out `t243`, where `t243` is used analogous to `i64` or `u64`. If the latter
//! are 64-bit signed/unsigned integer types, then `t243` is a 243-trit integer type.
//! Analogous to fanning out a `u64` into 64 individual bits, `t243` is fanned out into
//! 243 trits, each (rather inefficiently) represented by one `u8`.

use crate::{
    i384::{
        self,
        BigEndian,
        LittleEndian,
        I384,
    },
    TritsBuf,
    ValidTrits,
};
// use std::cmp::Ordering;

/// The number of trits in a T243
pub const LEN: usize = 243;

pub struct T243(TritsBuf);

impl T243 {
    fn zero() -> Self {
        let mut inner = TritsBuf::with_capacity(LEN);
        inner.fill(ValidTrits::Zero);
        Self(inner)
    }

    pub fn inner_ref(&self) -> &TritsBuf {
        &self.0
    }

    pub fn into_inner(self) -> TritsBuf {
        self.0
    }
}

impl Default for T243 {
    fn default() -> Self {
        Self::zero()
    }
}

impl From<I384<BigEndian, i384::U8Repr>> for T243 {
    fn from(value: I384<BigEndian, i384::U8Repr>) -> Self {
        let be_u32 = Into::<I384<BigEndian, i384::U32Repr>>::into(value);
        let le_u32= Into::<I384<LittleEndian, i384::U32Repr>>::into(be_u32);
        le_u32.into()
    }
}

impl From<I384<BigEndian, i384::U32Repr>> for T243 {
    fn from(value: I384<BigEndian, i384::U32Repr>) -> Self {
        let value_little_endian: I384<LittleEndian, i384::U32Repr> = value.into();
        value_little_endian.into()
    }
}

impl From<I384<LittleEndian, i384::U32Repr>> for T243 {
    fn from(value: I384<LittleEndian, i384::U32Repr>) -> Self {
        let mut value = value;

        // Shift the bigint from signed into unsigned positive space.
        // let flip_trits = if value.is_negative() {
        //     value.add_inplace(i384::LE_U32_TERNARY_0);
        //     false
        // } else {
        //     if value > i384::LE_U32_TERNARY_0 {
        //         value.sub_inplace(i384::LE_U32_TERNARY_0);
        //         true
        //     } else {
        //         value.add_integer_inplace(1u32);
        //         let mut tmp = i384::LE_U32_TERNARY_0;
        //         tmp.sub_inplace(value);
        //         value = tmp;
        //         false
        //     }
        // };
        value.add_inplace(i384::LE_U32_TERNARY_0);

        let mut trits_buf = T243::zero().into_inner();
        for trit in trits_buf.inner_mut() {
            let mut rem = 0;

            // Iterate over the digits of the bigint, starting from the most significant one.
            for digit in value.inner.iter_mut().rev() {
                let digit_with_rem = ((rem as u64) << 32) | *digit as u64;
                *digit = (digit_with_rem / 3u64) as u32;
                rem = (digit_with_rem % 3u64) as u32;
            }

            *trit = rem as i8 - 1i8;
        }

        T243(trits_buf)
    }
}
