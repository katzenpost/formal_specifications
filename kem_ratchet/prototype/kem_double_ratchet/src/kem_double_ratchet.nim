# SPDX-FileCopyrightText: (c) 2024 David Stainton
# SPDX-License-Identifier: AGPL-3.0-only

import secp256k1
import nimcrypto
import nimcrypto/blake2
import std/random
import std/options
import results
import std/tables
import sequtils


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

type CKAState* = object
  public_key*: Option[SkPublicKey]
  private_key*: Option[SKSecretKey]

proc update_state(self: var CKAState, update: CKAState) =
  self.public_key = update.public_key
  self.private_key = update.private_key

type CKAMessage = tuple
  public_key: SkPublicKey
  ciphertext: seq[byte]

proc initDefaultCKAMessage(st: CKAState): CKAMessage =
  return CKAMessage: (st.public_key.get(), newSeq[byte](65))

proc toRaw*(mesg: CKAMessage): seq[byte] =
  let public_key_raw = toRaw(mesg.public_key)
  return concat(toSeq(public_key_raw), mesg.ciphertext)

proc fromRaw*(raw_mesg: seq[byte]): CKAMessage =
  var raw_pub_key: array[65, byte]
  for i in 0..64:
    raw_pub_key[i] = raw_mesg[i]
  var cka_mesg: CKAMessage
  cka_mesg.public_key = SkPublicKey.fromRaw(raw_pub_key).expect("pub key")
  cka_mesg.ciphertext = newSeq[byte](len(raw_mesg)-65)
  var j = 65
  for i in 0..64:
    cka_mesg.ciphertext[i] = raw_mesg[j]
    j += 1
  return cka_mesg

proc cka_init_a*(seed: seq[byte]): CKAState =
  let (pk,_) = kem_gen_with_seed(seqToArrayByte(seed, 32)).expect("should be a keypair")
  let st: CKAState = CKAState(public_key: some(pk), private_key: none(SKSecretKey))
  return st

proc cka_init_b*(seed: seq[byte]): CKAState =
  let (_,sk) = kem_gen_with_seed(seqToArrayByte(seed, 32)).expect("should be a keypair")
  let st: CKAState = CKAState(public_key: none(SkPublicKey), private_key: some(sk))
  return st

proc cka_send*(state: var CKAState): (CKAMessage, seq[byte]) =
  assert state.public_key.isSome == true
  let (ct, ss) = kem_encap(state.public_key.get())
  let (pk, sk) = kem_gen()
  update_state(state, CKAState(public_key: state.public_key, private_key: some(sk)))
  let mesg: CKAMessage = (public_key: pk, ciphertext: ct)
  return (mesg, ss)

proc cka_receive*(state: var CKAState, mesg: CKAMessage): seq[byte] =
  assert state.private_key.isSome == true
  let ss = kem_decap(state.private_key.get(), mesg.ciphertext)
  let new_st = CKAState(public_key: some(mesg.public_key), private_key: some(state.private_key.get()))
  update_state(state, new_st)
  return ss

# AEAD

proc aead_key_gen*(): array[aes256.sizeKey, byte] =
  var key: array[aes256.sizeKey, byte]
  let _ = workingRng(key)
  return key

proc aead_encrypt*(key: array[aes256.sizeKey, byte], nonce: array[aes256.sizeBlock, byte], ad: seq[byte], mesg: seq[byte]): seq[byte] = 
  var ctx: GCM[aes256]
  ctx.init(key, nonce, ad)
  var ct = newSeq[byte](len(mesg))
  ctx.encrypt(mesg, ct)
  return ct

proc aead_decrypt*(key: array[aes256.sizeKey, byte], nonce: array[aes256.sizeBlock, byte], ad: seq[byte], ct: seq[byte]): seq[byte] =
  var ctx: GCM[aes256]
  ctx.init(key, nonce, ad)
  var plaintext = newSeq[byte](len(ct))
  ctx.decrypt(ct, plaintext)
  return plaintext

# PRG

type PRGState* = object
  data*: array[32, byte]

proc new_prg_state*(ikm: array[32, byte]): PRGState =
  return PRGState(data: ikm)

proc prg*(state: var PRGState, key: array[aes256.sizeKey, byte]): seq[byte] =
  var ctx: CTR[aes256]
  var iv: array[aes256.sizeBlock, byte]
  ctx.init(key, iv)
  let length = 32
  let zeros = newSeq[byte](32+length)
  var ct = newSeq[byte](32+length)
  ctx.encrypt(zeros, ct)
  for i in 0..31:
    state.data[i] = ct[i]
  var ret = newSeq[byte](length)
  var j = 0
  for i in 31..length:
    ret[j] = ct[i]
    j += 1
  return ret

# FS AEAD

type FSAEADState* = object
  data*: array[32, byte]
  index*: uint32
  receive_max*: uint32
  key_store*: Option[TableRef[uint32, array[32, byte]]]

proc fs_init_send*(ikm: array[32, byte]): FSAEADState =
  let st = FSAEADState(data: ikm, index:0, key_store: none(TableRef[uint32, array[32, byte]]))
  return st

proc fs_init_receive*(ikm: array[32, byte]): FSAEADState =
  let st = FSAEADState(data: ikm, index:0, key_store: some(new TableRef[uint32, array[32, byte]]))
  return st

type Byte = uint8
type FourByteArray = array[0..3, Byte]

proc uint32FromBytes(v: uint32): FourByteArray =
  result = cast[FourByteArray](v)

proc toUint32(FourByteArray: FourByteArray): uint32 =
  result = cast[uint32](FourByteArray)

proc fs_send*(st: var FSAEADState, ad: seq[byte], mesg: seq[byte]): (seq[byte],seq[byte]) =
  st.index += 1
  var prg_st = new_prg_state(st.data)
  let k = prg(prg_st, st.data)
  st.data = prg_st.data
  let index_bytes = uint32FromBytes(uint32(st.index))
  let index_seq = toSeq(index_bytes)
  let h = concat(index_seq, ad)
  var nonce: array[aes256.sizeBlock, byte]
  let ct = aead_encrypt(seqToArrayByte(k, 32), nonce, h, mesg)
  return (h,ct)

proc try_skipped(st: FSAEADState, index: uint32): (seq[byte],bool) =
  let table = st.key_store.get()
  return (toSeq(table.getOrDefault(index)),table.hasKey(index))

proc skip(st: var FSAEADState, index: uint32): void =
  while st.index < index-1:
    st.index += 1
    var prg_st = new_prg_state(st.data)
    let k = prg(prg_st, st.data)
    st.data = prg_st.data
    var table = st.key_store.get()
    table[st.index] = seqToArrayByte(k, 32)

proc fs_receive*(st: var FSAEADState, ad: seq[byte], ct: seq[byte]): seq[byte] =
  var index_raw: FourByteArray
  for i in 0..3:
    index_raw[i] = ad[i]
  let index = toUint32(index_raw)
  let (k,found) = try_skipped(st, index)
  var key = k
  if not found:
    skip(st, index)
    var prg_st = new_prg_state(st.data)
    key = prg(prg_st, st.data)
    st.data = prg_st.data
    st.index = index
  var nonce: array[aes256.sizeBlock, byte]
  return aead_decrypt(seqToArrayByte(key, 32), nonce, ad, ct)  

proc fs_stop(st: var FSAEADState): uint32 =
  var count: uint32 = 0
  for k, v in st.key_store.get():
    del(st.key_store.get(), k)
    count += 1
  return count

proc fs_max(st: var FSAEADState, max: uint32): void =
  st.receive_max = max

# PRF PRNG

include hkdf

type PRF_PRNG_State* = object
  key*: array[32,byte]

proc new_prf_prng_state*(ikm: array[32, byte]): PRF_PRNG_State =
  return PRF_PRNG_State(key: ikm)

proc up*(state: var PRF_PRNG_State, ikm: array[32, byte]): seq[byte] =
  var output: array[2, array[32, byte]]
  let info = fromHex("0xdeadbabecafebeefface")
  sha256.hkdf(state.key, ikm, info, output)
  state.key = output[0]
  return toSeq(output[1])

# modular KEM double ratchet

type RatchetState* = object
  is_a*: bool
  root_rng_st*: array[32,byte]
  fs_aead_states*: TableRef[uint32, FSAEADState]
  cka_state*: CKAState
  cka_mesg*: CKAMessage
  epoch_count*: uint32
  prev_send_count*: uint32

proc initRatchet*(seed: array[64,byte], is_a: bool): RatchetState =
  # id ← A
  # (kroot , kCKA ) ← k
  var rng_key: array[aes256.sizeKey, byte]
  for i in 0..31:
    rng_key[i] = seed[i]
  var cka_key: array[32, byte]
  var j = 31
  for i in 0..31:
    cka_key[i] = seed[j]
    j += 1
  
  # σroot ← P-Init(kroot )
  var prf_prng_state = new_prf_prng_state(rng_key)

  # (σroot , k) ← P-Up(σroot , λ)
  var default_prf_prng_key: array[32, byte]
  let k = up(prf_prng_state, default_prf_prng_key)
  var st = RatchetState(is_a: is_a, epoch_count: 0, prev_send_count:0)
  st.root_rng_st = seqToArrayByte(k,32)

  # v[·] ← λ
  st.fs_aead_states = new TableRef[uint32, FSAEADState]

  # v[0] ← FS-Init-R(k)
  if is_a:
    st.fs_aead_states[uint32(0)] = fs_init_receive(seqToArrayByte(k, 32))
  else:
    st.fs_aead_states[uint32(0)] = fs_init_send(seqToArrayByte(k, 32))

  # γ ← CKA-Init-A(kCKA )
  if is_a:
    st.cka_state = cka_init_a(toSeq(cka_key))
  else:
    st.cka_state = cka_init_b(toSeq(cka_key))
  return st

type RatchetHeader* = tuple
  epoch_count: uint32
  prev_send_count: uint32
  cka_mesg: CKAMessage

proc encodeHeader*(header: var RatchetHeader): seq[byte] =
  let epoch_count_raw = uint32FromBytes(header.epoch_count)
  let prev_send_count_raw = uint32FromBytes(header.prev_send_count)
  let cka_mesg_raw = toRaw(header.cka_mesg)
  return concat(concat(toSeq(epoch_count_raw), toSeq(prev_send_count_raw)), toSeq(cka_mesg_raw))

proc decodeHeader*(header: seq[byte]): RatchetHeader =
  var epoch_count_raw: FourByteArray
  var offset = 0
  for i in 0..3:
    epoch_count_raw[i] = header[offset]
    offset += 1
  let epoch_count = toUint32(epoch_count_raw)
  var prev_send_count_raw: FourByteArray
  for i in 0..3:
    prev_send_count_raw[i] = header[offset]
    offset += 1
  let prev_send_count = toUint32(prev_send_count_raw)
  var cka_mesg_raw = newSeq[byte](len(header)-8)
  for i in 0..len(header)-9:
    cka_mesg_raw[i] = header[offset]
    offset += 1
  let cka_mesg = fromRaw(cka_mesg_raw)
  var h: RatchetHeader
  h.epoch_count = epoch_count
  h.prev_send_count = prev_send_count
  h.cka_mesg = cka_mesg
  return h

proc send*(st: var RatchetState, mesg: seq[byte]): (seq[byte],seq[byte]) =
  var do_update = false
  var check_even = false
  if st.is_a:
    check_even = true
  else:
    check_even = false
  var is_even = false
  if st.epoch_count mod 2 == 0:
    is_even = true
  else:
    is_even = false
  if check_even and is_even:
    do_update = true
  if not check_even and  not is_even:
    do_update = true
  # if tcur is even
  if do_update:
    if st.epoch_count != 0 and st.epoch_count != 1:
      # `prv ← FS-Stop(v[tcur − 1])
      try:
        st.prev_send_count = st.fs_aead_states[st.epoch_count-1].fs_stop()
      except ref KeyError:
        echo "key not found in fs_aead_states"
        quit(1)
    # tcur ++
    st.epoch_count += 1
    # (γ, Tcur , I) ←$ CKA-S(γ)
    let (mesg, ss) = cka_send(st.cka_state)   
    st.cka_mesg = mesg
    var p_st = new_prf_prng_state(st.root_rng_st)
    # (σroot , k) ← P-Up(σroot , I)
    let k = up(p_st, seqToArrayByte(ss, 32))
    # v[tcur ] ← FS-Init-S(k)
    st.fs_aead_states[st.epoch_count] = fs_init_send(seqToArrayByte(k, 32))
  # h ← (tcur , Tcur , `prv )
  var h: RatchetHeader
  h.epoch_count = st.epoch_count
  h.prev_send_count = st.prev_send_count
  h.cka_mesg = st.cka_mesg
  let header_raw = encodeHeader(h)
  # (v[tcur ], e) ← FS-Send(v[tcur ], h, m)
  try:
    return fs_send(st.fs_aead_states[st.epoch_count], header_raw, mesg)
  except ref KeyError:
    echo "key not found in fs_aead_states"
    quit(1)

proc receive*(st: var RatchetState, ad: seq[byte], ciphertext: seq[byte]): seq[byte] =
  var index_raw = newSeq[byte](4)
  for i in 0..3:
    index_raw[i] = ad[i]
  var header_raw = newSeq[byte](len(ad)-4)
  var offset = 0
  for i in 4..len(ad)-1:
    header_raw[offset] = ad[i]
    offset += 1
  var header = decodeHeader(header_raw)
  if st.is_a:
    assert header.epoch_count mod 2 == 0 and header.epoch_count <= (st.epoch_count + 1)
  else:
    assert header.epoch_count mod 2 == 1 and header.epoch_count <= (st.epoch_count + 1)
  if header.epoch_count == (st.epoch_count + 1):
    st.epoch_count += 1
    if st.epoch_count != 1:
      try:
        fs_max(st.fs_aead_states[header.epoch_count-2], header.prev_send_count)
      except ref KeyError:
        echo "key not found in fs_aead_states"
        quit(1)
    let ss = cka_receive(st.cka_state, header.cka_mesg)
    var p_st = new_prf_prng_state(st.root_rng_st)
    let k = up(p_st, seqToArrayByte(ss, 32))
    try:
      st.fs_aead_states[header.epoch_count] = fs_init_receive(seqToArrayByte(k,32))
    except ref KeyError:
      echo "key not found in fs_aead_states"
      quit(1)
  try:
    return fs_receive(st.fs_aead_states[header.epoch_count], ad, ciphertext)
  except ref KeyError:
    echo "key not found in fs_aead_states"
    quit(1)

