# SPDX-FileCopyrightText: (c) 2024 David Stainton
# SPDX-License-Identifier: AGPL-3.0-only

import secp256k1
import sequtils
import nimcrypto/blake2
import nimcrypto/keccak
import std/random
import std/options
import results

# KEM

proc workingRng*(data: var openArray[byte]): bool =
  for i in 0..<data.len:
    data[i] = byte(rand(0..255))
  true

proc kem_gen*(): (SKPublicKey, SKSecretKey) =
  let sk = SkSecretKey.random(workingRng).expect("should get a key")
  let pk = sk.toPublicKey()
  return (pk, sk)

proc kem_gen_with_seed*(seed: array[32,byte]): Result[(SKPublicKey, SKSecretKey),string] =
  let skResult = SkSecretKey.fromRaw(seed)
  let sk = skResult.get()
  let pk = sk.toPublicKey()
  ok((pk, sk))

proc hash(ss:SkEcdhSecret, pk1:SKPublicKey, pk2:SKPublicKey): seq[byte] =
  let ss_blob = ss.data
  let pk1_blob = to_raw(pk1)
  let pk2_blob = to_raw(pk2)
  var ctx: blake2_256
  ctx.init()
  ctx.update(ss_blob)
  ctx.update(pk1_blob)
  ctx.update(pk2_blob)
  ctx.update(ss_blob)
  return toSeq(ctx.finish().data)

proc kem_encap*(pubKey: SKPublicKey): (seq[byte], seq[byte]) =
  let (pk, sk) = kem_gen()
  let kem_ciphertext = toSeq(to_raw(pk))
  let ss = ecdh(sk, pubKey)
  let ss2 = hash(ss, pubKey, pk)
  return (kem_ciphertext, ss2)

template seqToArrayByte(s: seq[byte], N: static[int]): array[N, byte] =
  var arr: array[N, byte]
  for i in 0..<N:
    arr[i] = s[i]
  arr

proc kem_decap*(privKey: SKSecretKey, ct: seq[byte]): seq[byte] =
  let pk_raw = seqToArrayByte(ct, SkRawPublicKeySize)
  let pk = SkPublicKey.fromRaw(pk_raw)[]
  let ss1 = ecdh(privKey, pk)
  let ss2 = hash(ss1, privKey.toPublicKey(), pk)
  return ss2

# CKA

type CKAState = tuple
  public_key: Option[SkPublicKey]
  private_key: Option[SKSecretKey]

type CKAMessage = tuple
  ciphertext: seq[byte]
  public_key: SkPublicKey

proc cka_init_a*(seed: seq[byte]): CKAState =
  let (pk,_) = kem_gen_with_seed(seqToArrayByte(seed, 32)).expect("should be a keypair")
  let st: CKAState = (public_key: some(pk), private_key: none(SKSecretKey))
  return st

proc cka_init_b*(seed: seq[byte]): CKAState =
  let (_,sk) = kem_gen_with_seed(seqToArrayByte(seed, 32)).expect("should be a keypair")
  let st: CKAState = (public_key: none(SkPublicKey), private_key: some(sk))
  return st

proc cka_send*(state: CKAState): (CKAState, CKAMessage, seq[byte]) =
  assert state.public_key.isSome == true
  let (ct, ss) = kem_encap(state.public_key.get())
  let (pk, sk) = kem_gen()
  let st: CKAState = (public_key: state.public_key, private_key: some(sk))
  let mesg: CKAMessage = (ciphertext: ct, public_key: pk)
  return (st, mesg, ss)

proc cka_receive*(state: CKAState, mesg: CKAMessage): (CKAState, seq[byte]) =
  assert state.private_key.isSome == true
  let ss = kem_decap(state.private_key.get(), mesg.ciphertext)
  let st: CKAState = (public_key: some(mesg.public_key), private_key: some(state.private_key.get()))
  return (st, ss)






