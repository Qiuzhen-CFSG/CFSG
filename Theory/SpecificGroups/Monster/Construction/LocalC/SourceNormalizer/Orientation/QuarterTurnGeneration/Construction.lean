module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurns
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift

/-!
# Constructing quarter turns of the actual extraspecial group

A nonsingular element `q` defines an automorphism that fixes its centralizer
and multiplies the other elements by `q`. Central commutator calculus proves
multiplicativity, and the square is conjugation by `q`, proving bijectivity.
Thus these inner conjugations lie in the quarter-turn subgroup. Automorphisms
trivial on the central quotient are inner by extraspecial commutator duality.

These are the group-theoretic steps toward the spin normalizer computation in
Aschbacher, *Sporadic Groups*, Exercise 4.4, p. 64, and Section 27, pp. 147–148.
The geometric generation assertion is not assumed here.
-/

public section
set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement IsMulCommutative
open Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

private theorem centerGenerator_mem_center :
    q1ImageCenterGenerator ∈ Subgroup.center Q1Image := by
  rw [Q1Image_center]
  exact Subgroup.mem_zpowers _

private theorem center_eq_one_or_generator {x : Q1Image}
    (hx : x ∈ Subgroup.center Q1Image) : x = 1 ∨ x = q1ImageCenterGenerator := by
  by_cases h : x = 1
  · exact Or.inl h
  · right
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q1Image)).mp
      Q1Image_center_card
    exact congrArg Subtype.val ((hw ⟨x,hx⟩ (by
      intro he; exact h (congrArg Subtype.val he))).trans
        (hw ⟨q1ImageCenterGenerator,centerGenerator_mem_center⟩ (by
          intro he; exact q1ImageCenterGenerator_ne_one (congrArg Subtype.val he))).symm)

private theorem commutator_mem_center (x y : Q1Image) :
    ⁅x,y⁆ ∈ Subgroup.center Q1Image := by
  let _ := Q1Image_central_quotient_elementary
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (Subgroup.center Q1Image)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private theorem commutator_of_not_commute {q x : Q1Image} (h : ¬ Commute q x) :
    ⁅q,x⁆ = q1ImageCenterGenerator := by
  exact (center_eq_one_or_generator (commutator_mem_center q x)).resolve_left
    (fun he => h (commutatorElement_eq_one_iff_commute.mp he))

private theorem commutator_mul (q x y : Q1Image) : ⁅q,x*y⁆ = ⁅q,x⁆ * ⁅q,y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    mul_assoc ⁅q,x⁆ x ⁅q,y⁆,
    Subgroup.mem_center_iff.mp (commutator_mem_center q y) x]
  simp only [← mul_assoc, mul_inv_cancel_right]

private def turn (q x : Q1Image) : Q1Image := by
  classical
  exact if Commute q x then x else q * x

private theorem turn_mul (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator)
    (x y : Q1Image) : turn q (x*y) = turn q x * turn q y := by
  classical
  have hh := commutator_mul q x y
  by_cases hx : Commute q x <;> by_cases hy : Commute q y
  · simp [turn, hx, hy, hx.mul_right hy]
  · have hxy : ¬ Commute q (x*y) := by
      intro hc
      rw [hx.commutator_eq, one_mul] at hh
      exact hy (commutatorElement_eq_one_iff_commute.mp (hh.symm.trans hc.commutator_eq))
    simp only [turn, if_neg hxy, if_pos hx, if_neg hy]
    rw [← mul_assoc, hx.eq, mul_assoc]
  · have hxy : ¬ Commute q (x*y) := by
      intro hc
      rw [hy.commutator_eq, mul_one] at hh
      exact hx (commutatorElement_eq_one_iff_commute.mp (hh.symm.trans hc.commutator_eq))
    simp [turn, hxy, hx, hy, mul_assoc]
  · have hxy : Commute q (x*y) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [hh,commutator_of_not_commute hx,commutator_of_not_commute hy,
        ← pow_two,q1ImageCenterGenerator_sq]
    simp only [turn, if_pos hxy, if_neg hx, if_neg hy]
    have hconj : q*x*q⁻¹ = q1ImageCenterGenerator*x := by
      rw [← commutator_of_not_commute hx,commutatorElement_def]
      group
    have hqxq : q*x*q = x := by
      calc
        q*x*q = (q*x*q⁻¹) * q^2 := by group
        _ = (q1ImageCenterGenerator*x) * q1ImageCenterGenerator := by rw [hconj,hq]
        _ = x := by
          rw [← Subgroup.mem_center_iff.mp centerGenerator_mem_center x,
            mul_assoc, ← pow_two, q1ImageCenterGenerator_sq, mul_one]
    rw [← mul_assoc, hqxq]

private theorem turn_square (q x : Q1Image) (hq : q^2 = q1ImageCenterGenerator) :
    turn q (turn q x) = MulAut.conj q x := by
  classical
  by_cases hx : Commute q x
  · simp only [turn, if_pos hx]
    exact hx.mul_inv_cancel.symm
  · have hqx : ¬ Commute q (q*x) := by
      simpa only [Commute, SemiconjBy, mul_assoc, mul_left_cancel_iff] using hx
    simp only [turn, if_neg hx, if_neg hqx]
    rw [← mul_assoc, ← pow_two, hq]
    rw [conj_eq_commutatorElement_mul, commutator_of_not_commute hx]

/-- The automorphism fixing the centralizer of `q` and multiplying its complement by `q`. -/
def quarterTurn (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator) : MulAut Q1Image :=
  MulEquiv.ofBijective
    (show Q1Image →* Q1Image from
      { toFun := turn q
        map_one' := by
          classical
          simp [turn]
        map_mul' := turn_mul q hq })
    (by
      have hi : Function.Injective (turn q) := by
        intro x y he
        apply (MulAut.conj q).injective
        rw [← turn_square q x hq, ← turn_square q y hq, he]
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

/-- The quarter turn has the prescribed action on both commutation classes. -/
theorem quarterTurn_spec (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator)
    (x : Q1Image) :
    (Commute q x → quarterTurn q hq x = x) ∧
      (¬ Commute q x → quarterTurn q hq x = q*x) := by
  classical
  constructor <;> intro h <;> change turn q x = _ <;> simp [turn,h]

/-- Every nonsingular element supplies a member of the published generating family. -/
theorem quarterTurn_mem (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator) :
    quarterTurn q hq ∈ quarterTurnAutomorphisms :=
  ⟨q,hq,quarterTurn_spec q hq⟩

/-- Squaring a quarter turn gives conjugation by its defining element. -/
theorem quarterTurn_sq (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator) :
    quarterTurn q hq ^ 2 = MulAut.conj q := by
  apply MulEquiv.ext
  intro x
  exact turn_square q x hq

/-- Inner conjugations by nonsingular elements belong to the quarter-turn subgroup. -/
theorem nonsingular_conj_mem (q : Q1Image) (hq : q^2 = q1ImageCenterGenerator) :
    MulAut.conj q ∈ Subgroup.closure quarterTurnAutomorphisms := by
  rw [← quarterTurn_sq q hq]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (quarterTurn_mem q hq)) 2


theorem automorphism_fixes_center (α : MulAut Q1Image) (x : Q1Image)
    (hx : x ∈ Subgroup.center Q1Image) : α x = x := by
  rcases center_eq_one_or_generator hx with rfl | rfl
  · exact map_one α
  · have hz : α q1ImageCenterGenerator ∈ Subgroup.center Q1Image :=
      (Subgroup.centerCongr α ⟨q1ImageCenterGenerator, centerGenerator_mem_center⟩).property
    exact (center_eq_one_or_generator hz).resolve_left (by
      intro h
      exact q1ImageCenterGenerator_ne_one (α.injective (h.trans (map_one α).symm)))

/-- The kernel of the actual action on the central quotient consists of inner automorphisms. -/
theorem exists_inner_of_trivial_quotient (α : MulAut Q1Image)
    (hα : ∀ x : Q1Image,
      QuotientGroup.mk' (Subgroup.center Q1Image) (α x) =
        QuotientGroup.mk' (Subgroup.center Q1Image) x) :
    ∃ q : Q1Image, α = MulAut.conj q := by
  let _ := Q1Image_extraspecial
  obtain ⟨r,hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
    (⊤ : Subgroup Q1Image) le_top α (automorphism_fixes_center α) (by
      intro x _
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (Subgroup.center Q1Image)) (α x * x⁻¹) = 1
      rw [map_mul,map_inv,hα,mul_inv_cancel])
  refine ⟨r⁻¹,?_⟩
  have he : α * MulAut.conj r = 1 := MulEquiv.ext fun x => hr x (by trivial)
  have hh := eq_inv_of_mul_eq_one_left he
  simpa using hh

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
