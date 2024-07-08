# This is just an example to get you started. You may wish to put all of your
# tests into a single file, or separate them into multiple `test1`, `test2`
# etc. files (better names are recommended, just make sure the name starts with
# the letter 't').
#
# To run these tests, simply execute `nimble test`.

import unittest
import kem_double_ratchet

suite "modular KEM double ratchet":
  test "KEM correctness":
    let (pk, sk) = kem_gen()
    let (ct, ss1) = kem_encap(pk)
    let ss2 = kem_decap(sk, ct)
    check:
      ss1 == ss2
