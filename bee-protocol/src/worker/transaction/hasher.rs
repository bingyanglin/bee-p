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

use crate::{
    message::{uncompress_transaction_bytes, Transaction as TransactionMessage},
    protocol::Protocol,
    worker::transaction::{HashCache, ProcessorWorkerEvent},
};

use bee_common::{shutdown_stream::ShutdownStream, worker::Error as WorkerError};
use bee_crypto::ternary::{
    sponge::{BatchHasher, CurlPRounds, BATCH_SIZE},
    Hash,
};
use bee_network::EndpointId;
use bee_ternary::{T5B1Buf, TritBuf, Trits, T5B1};
use bee_transaction::bundled::{BundledTransactionField, TRANSACTION_TRIT_LEN};

use bytemuck::cast_slice;
use futures::{
    channel::mpsc,
    stream::{Fuse, Stream, StreamExt},
    task::{Context, Poll},
};
use log::{info, trace, warn};
use pin_project::pin_project;

use std::pin::Pin;

// If a batch has less than this number of transactions, the regular CurlP hasher is used instead
// of the batched one.
const BATCH_SIZE_THRESHOLD: usize = 3;

type Receiver = ShutdownStream<Fuse<mpsc::UnboundedReceiver<HasherWorkerEvent>>>;

pub(crate) struct HasherWorkerEvent {
    pub(crate) from: EndpointId,
    pub(crate) transaction: TransactionMessage,
}

#[pin_project(project = HasherWorkerProj)]
pub(crate) struct HasherWorker {
    processor_worker: mpsc::UnboundedSender<ProcessorWorkerEvent>,
    #[pin]
    receiver: Receiver,
    cache: HashCache,
    hasher: BatchHasher<T5B1Buf>,
    events: Vec<HasherWorkerEvent>,
}

impl HasherWorker {
    pub(crate) fn new(
        processor_worker: mpsc::UnboundedSender<ProcessorWorkerEvent>,
        cache_size: usize,
        receiver: Receiver,
    ) -> Self {
        assert!(BATCH_SIZE_THRESHOLD <= BATCH_SIZE);
        Self {
            processor_worker,
            receiver,
            cache: HashCache::new(cache_size),
            hasher: BatchHasher::new(TRANSACTION_TRIT_LEN, CurlPRounds::Rounds81),
            events: Vec::with_capacity(BATCH_SIZE),
        }
    }

    fn trigger_hashing(&mut self, batch_size: usize) {
        if batch_size < BATCH_SIZE_THRESHOLD {
            let hashes = self.hasher.hash_unbatched();
            Self::send_hashes(hashes, &mut self.events, &mut self.processor_worker);
        } else {
            let hashes = self.hasher.hash_batched();
            Self::send_hashes(hashes, &mut self.events, &mut self.processor_worker);
        }
        // FIXME: we could store the fraction of times we use the batched hasher
    }

    fn send_hashes(
        hashes: impl Iterator<Item = TritBuf>,
        events: &mut Vec<HasherWorkerEvent>,
        processor_worker: &mut mpsc::UnboundedSender<ProcessorWorkerEvent>,
    ) {
        for (HasherWorkerEvent { from, transaction }, hash) in events.drain(..).zip(hashes) {
            if let Err(e) = processor_worker.unbounded_send(ProcessorWorkerEvent {
                hash: Hash::from_inner_unchecked(hash),
                from,
                transaction,
            }) {
                warn!("Sending event to the processor worker failed: {}.", e);
            }
        }
    }

    pub async fn run(mut self) -> Result<(), WorkerError> {
        info!("Running.");

        while let Some(batch_size) = self.next().await {
            self.trigger_hashing(batch_size);
        }

        info!("Stopped.");

        Ok(())
    }
}

impl Stream for HasherWorker {
    type Item = usize;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
        // We need to do this because `receiver` needs to be pinned to be polled.
        let HasherWorkerProj {
            mut receiver,
            hasher,
            events,
            cache,
            ..
        } = self.project();

        // We loop until we have `BATCH_SIZE` transactions or `stream.poll_next(cx)` returns
        // pending.
        loop {
            let batch_size = hasher.len();
            // If we already have `BATCH_SIZE` transactions, we are ready.
            if batch_size == BATCH_SIZE {
                return Poll::Ready(Some(BATCH_SIZE));
            }
            // Otherwise we need to check if there are transactions inside the `receiver` stream
            // that we could include in the current batch.
            match receiver.as_mut().poll_next(cx) {
                Poll::Pending => {
                    return if batch_size == 0 {
                        // If the stream is not ready yet and the current batch is empty we have to
                        // wait. Otherwise, we would end up hashing an empty batch.
                        Poll::Pending
                    } else {
                        // If the stream is not ready yet, but we have transactions in the batch,
                        // we can process them instead of waiting.
                        Poll::Ready(Some(batch_size))
                    };
                }
                Poll::Ready(Some(event)) => {
                    // If the transaction was already received, we skip it and poll again.
                    if !cache.insert(&event.transaction.bytes) {
                        trace!("Transaction already received.");
                        Protocol::get().metrics.known_transactions_inc();
                        continue;
                    }
                    // Given that the current batch has less than `BATCH_SIZE` transactions. We can
                    // add the transaction in the current event to the batch.
                    let transaction_bytes = uncompress_transaction_bytes(&event.transaction.bytes);

                    let trits = Trits::<T5B1>::try_from_raw(cast_slice(&transaction_bytes), TRANSACTION_TRIT_LEN)
                        .unwrap()
                        .to_buf::<T5B1Buf>();

                    hasher.add(trits);
                    events.push(event);
                    // If after adding the transaction to the batch its size is `BATCH_SIZE` we are
                    // ready to hash.
                    if batch_size == BATCH_SIZE - 1 {
                        return Poll::Ready(Some(BATCH_SIZE));
                    }
                }
                Poll::Ready(None) => {
                    // If the `receiver` stream ended, it means that either we should shutdown or
                    // the other side of the channel disconnected. In either case, we end this
                    // stream too without hashing the pending batch we have.
                    return Poll::Ready(None);
                }
            }
        }
    }
}
