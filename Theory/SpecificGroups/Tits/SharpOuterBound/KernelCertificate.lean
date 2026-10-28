module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Small checks for pointwise Sylow fixers

Six explicit words in each reflection overlap suffice to constrain the
reflection displacement. Commutation at point zero, together with the
order-five or involution relation, leaves one first displacement and two
second displacements. Every check is on the certified Atlas permutations.

Source: Parrott (1972), §5, p.683. The normal forms and left conjugation
convention are those of `Atlas1600SylowTwoCertificate`.
-/

@[expose] public section
namespace Tits.SharpOuterBound.KernelCertificate
open Atlas1600ParrottData Atlas1600SylowTwoCertificate
open OuterOddSubgroups.OverlapCentralizers

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

def firstWitness : Fin 6 → Fin 2048 := ![2, 16, 37, 128, 260, 1024]
def firstConjugate : Fin 6 → Fin 2048 := ![1024, 128, 2043, 16, 1753, 2]
def secondWitness : Fin 6 → Fin 2048 := ![1, 2, 4, 16, 32, 128]
def secondConjugate : Fin 6 → Fin 2048 := ![757, 128, 460, 16, 288, 2]

set_option maxRecDepth 20000

set_option maxHeartbeats 1600000 in
theorem first_conjugate (i : Fin 6) :
    r1Perm * normalForm (firstWitness i) * r1Perm = normalForm (firstConjugate i) := by
  have h : ∀ (i : Fin 6) (p : Fin 1600),
      (Packed.perm 0 * fastNormalForm (firstWitness i) * Packed.perm 0) p =
        fastNormalForm (firstConjugate i) p := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  apply Equiv.ext
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using h i

set_option maxHeartbeats 1600000 in
theorem second_conjugate (i : Fin 6) :
    r8Perm * normalForm (secondWitness i) * r8Perm = normalForm (secondConjugate i) := by
  have h : ∀ (i : Fin 6) (p : Fin 1600),
      (Packed.perm 1 * fastNormalForm (secondWitness i) * Packed.perm 1) p =
        fastNormalForm (secondConjugate i) p := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  apply Equiv.ext
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using h i

set_option maxHeartbeats 1600000 in
/-- Commutation and the order-five relation force trivial first displacement. -/
theorem first_displacement (n : Fin 2048)
    (hc : ∀ i : Fin 6, normalForm n (normalForm (firstWitness i) 0) =
      normalForm (firstWitness i) (normalForm n 0))
    (hp : ((s1Perm * r1Perm * normalForm n) ^ 5) 0 = 0) : n = 0 := by
  have h : ∀ n : Fin 2048,
      (∀ i : Fin 6, fastNormalForm n (fastNormalForm (firstWitness i) 0) =
        fastNormalForm (firstWitness i) (fastNormalForm n 0)) →
      ((Packed.perm 2 * Packed.perm 0 * fastNormalForm n) ^ 5) 0 = 0 → n = 0 := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  apply h n
  · simpa only [fastNormalForm_eq] using hc
  · simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using hp

set_option maxHeartbeats 1600000 in
/-- Commutation and the involution relation leave two second displacements. -/
theorem second_displacement (n : Fin 2048)
    (hc : ∀ i : Fin 6, normalForm n (normalForm (secondWitness i) 0) =
      normalForm (secondWitness i) (normalForm n 0))
    (hp : ((r8Perm * normalForm n) ^ 2) 0 = 0) : n = 0 ∨ n = 74 := by
  have h : ∀ n : Fin 2048,
      (∀ i : Fin 6, fastNormalForm n (fastNormalForm (secondWitness i) 0) =
        fastNormalForm (secondWitness i) (fastNormalForm n 0)) →
      ((Packed.perm 1 * fastNormalForm n) ^ 2) 0 = 0 → n = 0 ∨ n = 74 := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  apply h n
  · simpa only [fastNormalForm_eq] using hc
  · simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using hp

end Tits.SharpOuterBound.KernelCertificate
end
