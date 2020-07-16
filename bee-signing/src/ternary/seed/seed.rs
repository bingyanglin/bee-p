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

use bee_ternary::{TritBuf, Trits};

use zeroize::Zeroize;

pub trait Seed: Zeroize + Drop {
    type Error;

    fn new() -> Self;

    fn subseed(&self, index: u64) -> Self;

    fn from_trits(buf: TritBuf) -> Result<Self, Self::Error>
    where
        Self: Sized;

    fn to_trits(&self) -> &Trits;
}
