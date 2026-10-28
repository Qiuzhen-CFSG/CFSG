module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondCenterCertificate

/-!
# Finite tests for the intrinsic second Tits parabolic

Commutation modulo the known central involution, tested at point zero,
leaves four Sylow normal forms. The extra word identity
expresses the fourth candidate as the product of r5 and s1*s2*s3².
A final point test excludes the first reflection from their normalizer.
All finite tests are checked by the kernel; the existing generator-action
certificates are reused by the symbolic normalizer proof.

Source: Parrott (1972), p.683, in the certified Atlas permutation model.
-/

@[expose] public section

namespace Tits.RelativeParabolicNormalizers.SecondNormalizerCertificate
open Atlas1600ParrottData Atlas1600SylowTwoCertificate
open SecondCenterCertificate
set_option maxRecDepth 20000

def testPair (w g : Equiv.Perm (Fin 1600)) : Bool :=
  (w (g 0) == g (w 0)) || (w (g 0) == x (g (w 0)))

def testSecond (w : Equiv.Perm (Fin 1600)) : Bool :=
  testPair w s1Perm && testPair w s2Perm && testPair w s3Perm && testPair w s4Perm &&
  testPair w s5Perm && testPair w s6Perm && testPair w s7Perm && testPair w s8Perm

set_option maxHeartbeats 1600000 in
theorem candidates (i : Fin 2048) :
    testSecond (normalForm i) = true → i = 0 ∨ i = 11 ∨ i = 65 ∨ i = 74 := by
  revert i
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
theorem form_74 : normalForm 74 = x * y := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
theorem r1_y_out :
    (r1Perm * y * r1Perm⁻¹) 0 ≠ 0 ∧
    (r1Perm * y * r1Perm⁻¹) 0 ≠ x 0 ∧
    (r1Perm * y * r1Perm⁻¹) 0 ≠ y 0 ∧
    (r1Perm * y * r1Perm⁻¹) 0 ≠ (x * y) 0 := by decide +kernel

end Tits.RelativeParabolicNormalizers.SecondNormalizerCertificate

end
