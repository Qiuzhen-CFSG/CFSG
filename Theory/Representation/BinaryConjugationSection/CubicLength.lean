module

public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupAction.NoncentralTwoChiefLength.SectionMaps
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# Cubic lengths under binary contragredient duality

The binary relative sections occurring in the source duality have equal cubic
length on a common order-three actor. This packages the quotient transport and
contragredient fixed-index calculation used by the six-chief lower bound.
Source: Aschbacher--Smith, 13.7.4(2) and 13.7.12(1).
-/
public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]
  {H R N : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

theorem sectionCubicLength_eq_fixedIndex
    (s : BinaryConjugationSection H R N ρ)
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) :
    sectionCubicLength A N R = Nat.log 4 (BinaryFixedPoints.fixedIndex (ρ.comp (inclusion hAH))) := by
  let τ := ρ.comp (inclusion hAH)
  let := BinaryFixedPoints.action τ
  let d : ConjugationSection (Y := Multiplicative W) A N R (MonoidHom.id A) := {
    le := s.kernel_le
    normalizes := hAH.trans s.normalized
    projection := s.coordinates
    onto := s.onto
    kernel := s.kernel_eq
    equivariant a r := by
      apply Multiplicative.toAdd.injective
      exact s.equivariant (inclusion hAH a) r }
  exact d.length_eq hA hR Function.surjective_id


theorem dual_sectionCubicLength {R' N' : Subgroup G}
    (s : BinaryConjugationSection H R N ρ)
    (s' : BinaryConjugationSection H R' N' ρ.dual)
    (A : Subgroup G) (hAH : A ≤ H) (hAc : Nat.card A = 3)
    (hR : IsPGroup 2 R) (hR' : IsPGroup 2 R') :
    sectionCubicLength A N' R' = sectionCubicLength A N R := by
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAc)
  let : Finite W := Finite.of_surjective s.coordinates s.onto
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := A)
  rw [s'.sectionCubicLength_eq_fixedIndex A hAH hA hR',
    s.sectionCubicLength_eq_fixedIndex A hAH hA hR]
  exact congrArg (Nat.log 4) (BinaryFixedPoints.fixedIndex_dual
    (ρ.comp (inclusion hAH)) a ha)

end Representation.BinaryConjugationSection

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem sectionCubicLength_pos_of_commutator_not_le
    (A R N : Subgroup G) (hA : IsPGroup 3 A) (hR : IsPGroup 2 R)
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal]
    (hm : ¬ ⁅R,A⁆ ≤ N) : 1 ≤ sectionCubicLength A N R := by
  by_contra hn
  have hz : sectionCubicLength A N R = 0 := by omega
  let := quotientConjugationAction A R N hAR hAN
  have he := sectionCubicLength_eq_quotient_of_twoGroup A R N hA hR hNR hAR hAN
  rw [hz] at he
  have hi := FixedPoints.index_eq_four_pow_cubicLength (V := R ⧸ N.subgroupOf R)
    hA (hR.to_quotient _)
  rw [← he,pow_zero] at hi
  have htop : FixedPoints.subgroup A (R ⧸ N.subgroupOf R) = ⊤ := index_eq_one.mp hi
  apply hm
  rw [commutator_comm, commutator_le]
  intro a ha r hr
  have hfix : QuotientGroup.mk' (N.subgroupOf R) (⟨r,hr⟩ : R) ∈
      FixedPoints.subgroup A (R ⧸ N.subgroupOf R) := by rw [htop]; trivial
  have heq := hfix (⟨a,ha⟩ : A)
  have hh := QuotientGroup.eq_iff_div_mem.mp heq
  change a * r * a⁻¹ / r ∈ N at hh
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh
end Subgroup
