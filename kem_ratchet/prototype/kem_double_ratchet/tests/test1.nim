
import unittest
import kem_double_ratchet
import nimcrypto
import sequtils
import results
import nimcrypto

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

  test "AEAD correctness":
    var aliceAad = "Alice Authentication Data"
    var ad = newSeq[byte](len(aliceAad))
    copyMem(addr ad[0], addr aliceAad[0], len(aliceAad))
    var aliceData = "Alice hidden secret"
    var plainText = newSeq[byte](len(aliceData))
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

