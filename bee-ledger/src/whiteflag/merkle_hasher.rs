// Copyright 2020 IOTA Stiftung
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

use bee_crypto::ternary::Hash;
use bee_ternary::T5B1Buf;

use std::marker::PhantomData;

use bytemuck::cast_slice;
use digest::{Digest, Output};

/// Leaf domain separation prefix.
const LEAF_HASH_PREFIX: u8 = 0x00;
/// Node domain separation prefix.
const NODE_HASH_PREFIX: u8 = 0x01;

/// A Merkle hasher based on a digest function.
#[derive(Default)]
pub(crate) struct MerkleHasher<D: Default + Digest> {
    /// Type marker for the digest function.
    hasher: PhantomData<D>,
}

impl<D: Default + Digest> MerkleHasher<D> {
    /// Creates a new Merkle hasher.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Computes the largest power of two inferior to `n`.
    #[inline]
    fn largest_power_of_two(&self, n: u32) -> usize {
        1 << (32 - n.leading_zeros() - 1)
    }

    /// Returns the digest of the empty hash.
    fn empty(&mut self) -> Output<D> {
        D::digest(b"")
    }

    /// Returns the digest of a Merkle leaf.
    fn leaf(&mut self, hash: Hash) -> Output<D> {
        let mut hasher = D::default();

        hasher.update([LEAF_HASH_PREFIX]);
        hasher.update(cast_slice(hash.encode::<T5B1Buf>().as_i8_slice()));
        hasher.finalize_reset()
    }

    /// Returns the digest of a Merkle node.
    fn node(&mut self, hashes: &[Hash]) -> Output<D> {
        let mut hasher = D::default();
        let (left, right) = hashes.split_at(self.largest_power_of_two(hashes.len() as u32 - 1));

        hasher.update([NODE_HASH_PREFIX]);
        hasher.update(self.digest_inner(left));
        hasher.update(self.digest_inner(right));
        hasher.finalize_reset()
    }

    /// Returns the digest of a list of hashes as an `Output<D>`.
    fn digest_inner(&mut self, hashes: &[Hash]) -> Output<D> {
        match hashes.len() {
            0 => self.empty(),
            1 => self.leaf(hashes[0]),
            _ => self.node(hashes),
        }
    }

    /// Returns the digest of a list of hashes as a `Vec<u8>`.
    pub(crate) fn digest(&mut self, hashes: &[Hash]) -> Vec<u8> {
        self.digest_inner(hashes).to_vec()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use bee_ternary::{T1B1Buf, TryteBuf};
    use bee_transaction::bundled::BundledTransactionField;

    use blake2::Blake2b;

    #[test]
    fn empty() {
        let hash = MerkleHasher::<Blake2b>::new().digest(&[]);

        assert_eq!(
            hex::encode(hash),
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b14\
            48b755d56f701afe9be2ce"
        )
    }

    #[test]
    fn null_leaf() {
        let hash = MerkleHasher::<Blake2b>::new().digest(&vec![Hash::zeros()]);

        assert_eq!(
            hex::encode(hash),
            "0c18f7cbf23c3c8eda01ab64c79379ff0bf0d854125cbdf7dba43ca7630171d84c042673b731cb9f92cf937d738152306a8db092d9\
            413d531dd8a4299c05278f"
        )
    }

    #[test]
    fn null_node() {
        let hash = MerkleHasher::<Blake2b>::new().digest(&vec![Hash::zeros(), Hash::zeros()]);

        assert_eq!(
            hex::encode(hash),
            "876b38297f865de8b89fa69d7daa4da0fc31f562228ac4b5b71009ec10e878a7aec06f48ddf98a16460b742673ed47f308ff577684\
            26bf72a6aee27d1c4ba5fd"
        )
    }

    #[test]
    fn tree() {
        let mut hashes = Vec::new();

        for hash in [
            "NOBKDFGZMOWYUKDZITTWBRWA9YPSXCVFENCQFPC9GMJIAIPSSURYIOMYZLGNZXLUAQHHNBSRHNOIJDYZO",
            "IPATPTEZSBMFJRDCRPTCVUQWBAVCAXAVZIDEDL9TSILDFWDMIIFPZIYHKRFFZDYQNKBQBVGYSKMLCYBMR",
            "MXOIOFOGLIHCHMDRCWAIYCWIUCMGEZWXFJZFWBRCNSNBWIGFJXBCACPKMLLANYNXSGYKANYFTVGTLFXXX",
            "EXZTJAXJMZJBBIZGUTMBOEUQDNVHJPXCLFUXNLPLSBATDMKYUZOFMHCOBWUABYDMNGMKIXLIUFXNVY9PN",
            "SJXYVFUDCDPPAOALVXDQUKAWLLOQO99OSJQT9TUNILQ9VLFLCZMLZAKUTIZFHOLPMGPYHKMMUUSURIOCF",
            "Q9GHMAITEZCWKFIESJARYQYMF9XWFPQTTFRXULLHQDWEZLYBSFYHSLPXEHBORDDFYZRFYFGDCM9VJKEFR",
            "GMNECTSPSLSPPEITCHBXSN9KZD9OZPVPOET9TVQJDZMFGN9SGPRPMUQARNXUVKMWAFAKLKWBZLWZCTPCP",
        ]
        .iter()
        {
            hashes.push(Hash::from_inner_unchecked(
                TryteBuf::try_from_str(hash).unwrap().as_trits().encode::<T1B1Buf>(),
            ));
        }

        let hash = MerkleHasher::<Blake2b>::new().digest(&hashes);

        assert_eq!(
            hex::encode(hash),
            "d07161bdb535afb7dbb3f5b2fb198ecf715cbd9dfca133d2b48d67b1e11173c6f92bed2f4dca92c36e8d1ef279a0c19ca9e40a113e\
            9f5526090342988f86e53a"
        )
    }
}
