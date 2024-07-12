
import unittest
import kem_double_ratchet
import nimcrypto
import sequtils
import results
import secp256k1


suite "modular KEM double ratchet":
  test "KEM correctness":
    let (pk, sk) = kem_gen()
    let (ct, ss1) = kem_encap(pk)
    let ss2 = kem_decap(sk, ct)
    check:
      ss1 == ss2

  test "KEM gen from seed":
    var seed: array[32, byte]
    let _ = workingRng(seed)
    let seed_seq = seed
    let (pk,sk) = kem_gen_with_seed(seed_seq).expect("key pair from seed")
    let (ct, ss1) = kem_encap(pk)
    let ss2 = kem_decap(sk, ct)
    check:
      ss1 == ss2

  test "KEM pub key encoding":
    let (pk, sk) = kem_gen()
    let pk_raw = toRaw(pk)
    let pk2 = SkPublicKey.fromRaw(pk_raw).expect("pub key")
    let (ct, ss1) = kem_encap(pk2)
    let ss2 = kem_decap(sk, ct)
    check:
      ss1 == ss2

  test "CKA correctness":
    var seed: array[32, byte]
    let _ = randomBytes(seed)
    var alice_st = cka_init_a(toSeq(seed))
    var bob_st = cka_init_b(toSeq(seed))
    let (mesg1, ss) = cka_send(alice_st)
    let ss2 = cka_receive(bob_st, mesg1)
    check ss == ss2
    let (mesg2, ss3) = cka_send(bob_st)
    let ss4 = cka_receive(alice_st, mesg2)
    check ss3 == ss4

  test "CKA Message encoding decoding":
    var seed: array[32, byte]
    let _ = randomBytes(seed)
    var alice_st = cka_init_a(toSeq(seed))
    var bob_st = cka_init_b(toSeq(seed))
    let (mesg1, ss) = cka_send(alice_st)
    let mesg1_raw = toRaw(mesg1)
    let mesg1a = fromRaw(mesg1_raw)
    let ss2 = cka_receive(bob_st, mesg1a)
    check ss == ss2
    let (mesg2, ss3) = cka_send(bob_st)
    let mesg2_raw = toRaw(mesg2)
    let mesg2a = fromRaw(mesg2_raw)
    let ss4 = cka_receive(alice_st, mesg2a)
    check ss3 == ss4

  test "AEAD correctness":
    var aliceAad = "Alice Authentication Data"
    var ad = newSeq[byte](len(aliceAad))
    copyMem(addr ad[0], addr aliceAad[0], len(aliceAad))
    var aliceData = "Alice hidden secret"
    var plainText = newSeq[byte](len(aliceData))
    copyMem(addr plainText[0], addr aliceData[0], len(aliceData))
    let key = aead_key_gen()
    var nonce: array[aes256.sizeBlock, byte]
    let _ = workingRng(nonce)
    let ct = aead_encrypt(key, nonce, ad, plaintext)
    let plaintext2 = aead_decrypt(key, nonce, ad, ct)
    check plaintext == plaintext2
    let wrong_key = aead_key_gen()
    try:
      let plaintext3 = aead_decrypt(wrong_key, nonce, ad, ct)
    except:
      discard

  test "PRG smoke test":
    var state: array[32, byte]
    let _ = workingRng(state)
    var state_orig: array[32, byte]
    for i in 0..31:
      state_orig[i] = state[i]
    var prg_state = new_prg_state(state)
    let key = aead_key_gen()
    var ct = prg(prg_state, key)
    check:
      prg_state.data != state_orig
      ct.len == 32

  test "FS AEAD correctness":
    var seed: array[32, byte]
    let _ = workingRng(seed)
    var alice_st = fs_init_send(seed)
    var bob_st = fs_init_receive(seed)
    var aliceAad = "Alice Authentication Data"
    var ad1 = newSeq[byte](len(aliceAad))
    copyMem(addr ad1[0], addr aliceAad[0], len(aliceAad))
    var aliceData = "Alice hidden secret"
    var payload1 = newSeq[byte](len(aliceData))
    copyMem(addr payload1[0], addr aliceData[0], len(aliceData))
    let (ad1_i, ct1) = fs_send(alice_st, ad1, payload1)
    let payload2 = fs_receive(bob_st, ad1_i, ct1)
    check:
      payload1 == payload2

  test "Double Ratchet Header encoding decoding":
    var seed: array[32, byte]
    let _ = randomBytes(seed)
    var alice_st = cka_init_a(toSeq(seed))
    let (cka_mesg, _) = cka_send(alice_st)
    var h: RatchetHeader
    h.epoch_count = 345
    h.prev_send_count = 123
    h.cka_mesg = cka_mesg
    let header_raw = encodeHeader(h)
    let h2 = decodeHeader(header_raw)
    check:
      h.epoch_count == h2.epoch_count
      h.prev_send_count == h2.prev_send_count
      h.cka_mesg == h2.cka_mesg

  test "PRF PRNG smoke test":
    var seed1: array[32, byte]
    let _ = randomBytes(seed1)
    var p_st = new_prf_prng_state(seed1)

    var seed2: array[32, byte]
    let _ = workingRng(seed2)
    let output = up(p_st, seed2)

  test "Double Ratchet correctness":
    var seed: array[64, byte]
    let _ = workingRng(seed)
    var alice_ratchet = initRatchet(seed, true)
    var bob_ratchet = initRatchet(seed, false)

    var alice_mesg_raw = "Alice Secret Message"
    var alice_mesg = newSeq[byte](len(alice_mesg_raw))
    copyMem(addr alice_mesg[0], addr alice_mesg_raw[0], len(alice_mesg_raw))
    let (ad,ct) = send(alice_ratchet, alice_mesg)
    let plaintext = receive(bob_ratchet, ad, ct)
    check:
      plaintext == alice_mesg
