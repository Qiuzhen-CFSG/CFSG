module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.TwoGroup
public import Mathlib.GroupTheory.Abelianization.Defs

/-!+# Qualifying max1 copies for maximal-subgroup conjugacy

Every subgroup isomorphic to literal max1 has its certified order and index.
It is proper, since the model has an element of order 37. If that index is
odd, an internal Sylow two-subgroup gives an ambient Sylow contained in the
copy; this need not be the Sylow in the source-local hypothesis.

The checked max2 quotient bounds give quotient order 2661120, and its kernel
is a two-group. Thus 23 does not divide the order of literal max2. The same
exclusion follows for max4 from its proposed two-core quotient isomorphism.
Given the maximal-Sylow cover, these exclusions force a maximal overgroup of
a max1 copy to have the same order as that copy, proving maximality.

The model is also perfect without an order or simplicity hypothesis: in its
abelianization the image of `ab` has both fourth and thirty-seventh power one,
and the checked normal-generation certificate for `ab` kills the quotient.

Source: the Sylow-overgroup argument in Aschbacher–Smith A.3.12(17), printed
pp.47–48, used in 1.3.9, p.514; GLS3 Table 5.3i. Literal subgroup and matrix
provenance is retained in the imported certificate modules. The maximal
cover, odd index, and max4 quotient remain explicit unproved inputs here.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
namespace CandidateConjugacyReduction

open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- The supplied abstract comparison does transport the certified order. -/
theorem max1_copy_card {H : Subgroup Janko4.Model}
    (e : H ≃* certifiedMathieuSubgroup) : Nat.card H = 501397585920 :=
  (Nat.card_congr e.toEquiv).trans
    (by simpa only [certifiedMathieuSubgroup] using
      Janko4.Cardinality.max1Subgroup_card Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- The order-37 word in the actual model excludes a max1 copy being top. -/
theorem max1_copy_ne_top {H : Subgroup Janko4.Model}
    (e : H ≃* certifiedMathieuSubgroup) : H ≠ ⊤ := by
  intro ht
  have hd : 37 ∣ Nat.card H := by
    rw [ht, card_top, ← Janko4.orderOf_a_mul_b]
    exact orderOf_dvd_natCard (Janko4.a * Janko4.b)
  rw [max1_copy_card e] at hd
  norm_num at hd

/-- Equal subgroup orders give equal indices in this same finite ambient group. -/
theorem max1_copy_index {H : Subgroup Janko4.Model}
    (e : H ≃* certifiedMathieuSubgroup) : H.index = certifiedMathieuSubgroup.index := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
  rw [H.card_mul_index, Nat.card_congr e.toEquiv, certifiedMathieuSubgroup.card_mul_index]

/-- Odd literal index supplies an ambient Sylow inside any max1 copy.
This constructs a new Sylow and asserts no containment for the original S. -/
theorem exists_sylow_le_max1_copy {H : Subgroup Janko4.Model}
    (e : H ≃* certifiedMathieuSubgroup) (hindex : ¬ 2 ∣ certifiedMathieuSubgroup.index) :
    ∃ P : Sylow 2 Janko4.Model, P.toSubgroup ≤ H := by
  let T : Sylow 2 H := Sylow.nonempty.some
  have hQ : ¬ 2 ∣ ((T : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype, max1_copy_index e]
    exact Nat.Prime.not_dvd_mul Fact.out T.not_dvd_index hindex
  exact ⟨(T.2.map H.subtype).toSylow hQ, map_subtype_le _⟩

/-- Normal generation by the order-37 word proves perfectness of the matrix model.
This is a theorem, not a new global instance. -/
theorem model_isPerfect : Group.IsPerfect Janko4.Model := by
  let q : Janko4.Model →* Abelianization Janko4.Model := Abelianization.of
  have ha : q Janko4.a ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, ← map_pow, Janko4.a_pow_two, map_one, one_pow]
  have hb : q Janko4.b ^ 4 = 1 := by
    rw [← map_pow, Janko4.b_pow_four, map_one]
  have hr4 : q (Janko4.a * Janko4.b) ^ 4 = 1 := by
    rw [map_mul, mul_pow, ha, hb, one_mul]
  have hr37 : q (Janko4.a * Janko4.b) ^ 37 = 1 := by
    rw [← map_pow, ← Janko4.orderOf_a_mul_b, pow_orderOf_eq_one, map_one]
  have hr : q (Janko4.a * Janko4.b) = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 37)).mp ⟨hr4, hr37⟩
  have hgen : normalClosure ({Janko4.a * Janko4.b} : Set Janko4.Model) = ⊤ := by
    exact Janko4.Simplicity.normalClosure_primeRepresentative_eq_top
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four 10
  apply Group.isPerfect_def.mpr
  apply top_unique
  rw [← hgen]
  apply normalClosure_le_normal
  rintro x rfl
  rw [← Abelianization.ker_of Janko4.Model]
  exact hr

/-- The actual max2 quotient has order 2661120 and two-group kernel.
No equality with the whole involution centralizer is required. -/
theorem max2_card_not_dvd_23 : ¬ 23 ∣ Nat.card sourceSubgroup := by
  have hupper : Nat.card LocalNormalClosureQuotient ≤ 2661120 :=
    NormalClosureControl.ActionKernel.Presentation.quotient_card_le_of_presentation_bound
      NormalClosureControl.ActionKernel.Presentation.presentation_finite_card_le
  have hlower : 2661120 ≤ Nat.card LocalNormalClosureQuotient :=
    (LowerBound.quotientSubgroup_card_ge.trans
      quotientSubgroup_card_le_localNormalClosureOuterAction_range).trans
      (Nat.card_le_card_of_surjective _ localNormalClosureOuterAction.rangeRestrict_surjective)
  have heq := le_antisymm hupper hlower
  obtain ⟨n, hn⟩ := localNormalClosure_isPGroup.exists_card_eq
  rw [card_sourceSubgroup_eq_localSubgroup,
    card_eq_card_quotient_mul_card_subgroup localNormalClosure, heq, hn]
  exact ((by decide : Nat.Prime 23).coprime_iff_not_dvd).mp
    ((by decide : Nat.Coprime 23 2661120).mul_right
      ((by decide : Nat.Coprime 23 2).pow_right n))

/-- The proposed max4 quotient has order 20160; its two-core adds no prime 23.
The actual quotient equivalence remains a premise. -/
theorem max4_card_not_dvd_23
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) :
    ¬ 23 ∣ Nat.card max4Subgroup := by
  have hc : Nat.card QuotientModel = 20160 := by
    rw [Nat.card_prod, Atlas.Comparisons.Exceptional.sl3Two_card]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := max4Subgroup)).exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 max4Subgroup),
    Nat.card_congr e4.toEquiv, hc, hn]
  exact ((by decide : Nat.Prime 23).coprime_iff_not_dvd).mp
    ((by decide : Nat.Coprime 23 20160).mul_right
      ((by decide : Nat.Coprime 23 2).pow_right n))

/-- The maximal-Sylow cover and the prime-23 exclusions make a max1 copy maximal.
Ambient simplicity and normality of its source-local section are unnecessary. -/
theorem max1_copy_isCoatom_of_cover {H : Subgroup Janko4.Model}
    (e : H ≃* certifiedMathieuSubgroup) (hindex : ¬ 2 ∣ certifiedMathieuSubgroup.index)
    (hcover : MaximalSylowCover)
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) : IsCoatom H := by
  obtain ⟨P, hPH⟩ := exists_sylow_le_max1_copy e hindex
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left (max1_copy_ne_top e)
  have hdiv : 23 ∣ Nat.card M := by
    apply dvd_trans (b := Nat.card H) _ (card_dvd_of_le hHM)
    rw [max1_copy_card e]
    norm_num
  rcases hcover P M hM (hPH.trans hHM) with hf | hf | hf
  · obtain ⟨f⟩ := hf
    have heq : H = M := eq_of_le_of_card_ge hHM (by rw [max1_copy_card e, max1_copy_card f])
    exact heq.symm ▸ hM
  · obtain ⟨f⟩ := hf
    exact (max2_card_not_dvd_23 ((Nat.card_congr f.toEquiv) ▸ hdiv)).elim
  · obtain ⟨f⟩ := hf
    exact (max4_card_not_dvd_23 e4 ((Nat.card_congr f.toEquiv) ▸ hdiv)).elim

end CandidateConjugacyReduction
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
