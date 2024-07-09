# This is just an example to get you started. You may wish to put all of your
# tests into a single file, or separate them into multiple `test1`, `test2`
# etc. files (better names are recommended, just make sure the name starts with
# the letter 't').
#
# To run these tests, simply execute `nimble test`.


import unittest
import kem_double_ratchet
import nimcrypto
import sequtils
import results

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
    let alice_st = cka_init_a(toSeq(seed))
    let bob_st = cka_init_b(toSeq(seed))

    let (alice_st2, mesg1, ss) = cka_send(alice_st)
    let (bob_st2, ss2) = cka_receive(bob_st, mesg1)
    check ss == ss2
    
    let (bob_st3, mesg2, ss3) = cka_send(bob_st2)
    let (alice_st3, ss4) = cka_receive(alice_st2, mesg2)
    check ss3 == ss4
