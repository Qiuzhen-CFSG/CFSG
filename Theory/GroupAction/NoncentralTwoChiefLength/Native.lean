module
public import Theory.GroupAction.NoncentralTwoChiefLength
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic

/-!
# Cubic length on actual relative subgroup quotients

Express the cubic fixed-point invariant as the logarithm of the relative
centralizer index. Monotonicity gives subquotient comparison and differences
telescope along subgroup chains. Coprime lifting identifies these differences
with the lengths of the literal quotient conjugation actions.

This is the relative-normality interface for Aschbacher–Smith 13.8.33,
printed p.968; no normality in an ambient simple group is required.
-/

@[expose] public section

namespace Subgroup
variable {G : Type*} [Group G]

/-- Cubic length of the actual conjugation action, expressed intrinsically. -/
noncomputable def conjugationCubicLength (A R : Subgroup G) : ℕ :=
  Nat.log 4 ((centralizer (A : Set G)).relIndex R)

/-- Section contribution, which will be identified with quotient length under
coprime normalization and relative normality. -/
noncomputable def sectionCubicLength (A N R : Subgroup G) : ℕ :=
  conjugationCubicLength A R - conjugationCubicLength A N

theorem conjugationCubicLength_mono [Finite G] (A : Subgroup G)
    {R S : Subgroup G} (hRS : R ≤ S) :
    conjugationCubicLength A R ≤ conjugationCubicLength A S := by
  apply Nat.log_mono_right
  exact (centralizer (A : Set G)).relIndex_le_of_le_right hRS
    (Subgroup.FiniteIndex.index_ne_zero (H := (centralizer (A : Set G)).subgroupOf S))

theorem sectionCubicLength_mono [Finite G] (A : Subgroup G)
    {N R N' R' : Subgroup G} (hN : N' ≤ N) (hR : R ≤ R') :
    sectionCubicLength A N R ≤ sectionCubicLength A N' R' := by
  have hr := conjugationCubicLength_mono A hR
  have hn := conjugationCubicLength_mono A hN
  unfold sectionCubicLength
  omega

theorem sectionCubicLength_add [Finite G] (A : Subgroup G)
    {N R S : Subgroup G} (hNR : N ≤ R) (hRS : R ≤ S) :
    sectionCubicLength A N R + sectionCubicLength A R S = sectionCubicLength A N S := by
  have h₁ := conjugationCubicLength_mono A hNR
  have h₂ := conjugationCubicLength_mono A hRS
  unfold sectionCubicLength
  omega

@[simp] theorem conjugationCubicLength_bot (A : Subgroup G) :
    conjugationCubicLength A ⊥ = 0 := by
  simp [conjugationCubicLength]

/-- The definition is the invariant of the literal conjugation action. -/
theorem conjugationCubicLength_eq (A R : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G)) :
    letI := conjMulDistribMulActionOfLeNormalizer A R hAR
    conjugationCubicLength A R = FixedPoints.cubicLength A R := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  have hc : FixedPoints.subgroup A R = (centralizer (A : Set G)).subgroupOf R := by
    ext r
    constructor
    · intro hr
      apply mem_centralizer_iff.mpr
      intro a ha
      have he := congrArg Subtype.val (hr ⟨a, ha⟩)
      change a * (r : G) * a⁻¹ = (r : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hr a
      apply Subtype.ext
      change (a : G) * (r : G) * (a : G)⁻¹ = (r : G)
      have hh := mem_centralizer_iff.mp hr a a.property
      change (a : G) * (r : G) = (r : G) * (a : G) at hh
      rw [hh, mul_inv_cancel_right]
  unfold conjugationCubicLength FixedPoints.cubicLength
  rw [hc]
  rfl

/-- The actual conjugation action on a relative quotient. -/
@[reducible] noncomputable def quotientConjugationAction (A R N : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G)) (hAN : A ≤ normalizer (N : Set G))
    [(N.subgroupOf R).Normal] : MulDistribMulAction A (R ⧸ N.subgroupOf R) := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  have hInv : IsInvariant A R (N.subgroupOf R) :=
    ⟨fun a r => mem_normalizer_iff.mp (hAN a.property) r⟩
  exact quotientMulDistribMulAction (N.subgroupOf R) hInv

/-- Conjugation length differences equal the invariant of the actual quotient.
All normality is relative to `R`, including when `N` is not normal in any
larger local overgroup. -/
theorem sectionCubicLength_eq_quotient [Finite G] (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hsolv : Group.IsSolvable R)
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal] :
    letI := quotientConjugationAction A R N hAR hAN
    sectionCubicLength A N R = FixedPoints.cubicLength A (R ⧸ N.subgroupOf R) := by
  let := conjMulDistribMulActionOfLeNormalizer A R hAR
  let hInv : IsInvariant A R (N.subgroupOf R) :=
    ⟨fun a r => mem_normalizer_iff.mp (hAN a.property) r⟩
  let := hInv
  let := quotientMulDistribMulAction (N.subgroupOf R) hInv
  have hi := FixedPoints.cubicLength_eq_quotient_add_subgroup hA hR hsolv
    (N.subgroupOf R) hInv
  let := conjMulDistribMulActionOfLeNormalizer A N hAN
  have hn : FixedPoints.cubicLength A (N.subgroupOf R) = conjugationCubicLength A N := by
    rw [conjugationCubicLength_eq A N hAN]
    apply FixedPoints.cubicLength_eq_of_equivariant (subgroupOfEquivOfLe hNR)
    intro a n
    apply Subtype.ext
    rfl
  rw [hn, ← conjugationCubicLength_eq A R hAR] at hi
  unfold sectionCubicLength
  change conjugationCubicLength A R - conjugationCubicLength A N =
    FixedPoints.cubicLength A (R ⧸ N.subgroupOf R)
  omega

/-- For the finite two-group applications, solvability follows from the
prime-power hypothesis and is not an additional premise. -/
theorem sectionCubicLength_eq_quotient_of_twoGroup [Finite G] (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R)
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal] :
    letI := quotientConjugationAction A R N hAR hAN
    sectionCubicLength A N R = FixedPoints.cubicLength A (R ⧸ N.subgroupOf R) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := hR.isNilpotent
  exact sectionCubicLength_eq_quotient A R N hA hR inferInstance hNR hAR hAN

end Subgroup
