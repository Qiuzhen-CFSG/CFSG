module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Point certificates excluding non-Sylow parabolic cosets

Commutation with `s2` at point zero excludes all four nonzero cosets in the
first parabolic. Commutation with `s7` does the same for the two nonzero
cosets in the second parabolic. The finite checks use certified packed
versions of the actual Atlas1600 permutations.
Source: Parrott (1972), p.683; see `Packed` for the table certificate.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups.OverlapCentralizers.Certificate
open Atlas1600ParrottData Atlas1600SylowTwoCertificate

private def fastNormalForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) *
    Packed.perm 3 ^ (n.val / 2 % 2) *
    Packed.perm 4 ^ (n.val / 4 % 4) *
    Packed.perm 5 ^ (n.val / 16 % 2) *
    Packed.perm 6 ^ (n.val / 32 % 4) *
    Packed.perm 7 ^ (n.val / 128 % 2) *
    Packed.perm 8 ^ (n.val / 256 % 4) *
    Packed.perm 9 ^ (n.val / 1024 % 2)

private theorem fastNormalForm_eq (n : Fin 2048) : fastNormalForm n = normalForm n := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, normalForm]

def testPair (w g : Equiv.Perm (Fin 1600)) : Bool :=
  w (g 0) == g (w 0)

def testFirst (w : Equiv.Perm (Fin 1600)) : Bool := testPair w s2Perm

def testSecond (w : Equiv.Perm (Fin 1600)) : Bool := testPair w s7Perm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem first_coset_zero (n : Fin 2048) (j : Fin 5) :
    testFirst (normalForm n * (s1Perm * r1Perm) ^ j.val) = true → j = 0 := by
  have h : ∀ (n : Fin 2048) (j : Fin 5),
      testPair (fastNormalForm n * (Packed.perm 2 * Packed.perm 0) ^ j.val)
        (Packed.perm 3) = true → j = 0 := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator, testFirst] using h n j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem second_coset_zero (n : Fin 2048) (j : Fin 3) :
    testSecond (normalForm n * (s8Perm * r8Perm) ^ j.val) = true → j = 0 := by
  have h : ∀ (n : Fin 2048) (j : Fin 3),
      testPair (fastNormalForm n * (Packed.perm 9 * Packed.perm 1) ^ j.val)
        (Packed.perm 8) = true → j = 0 := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator, testSecond] using h n j

end Tits.OuterOddSubgroups.OverlapCentralizers.Certificate
end
