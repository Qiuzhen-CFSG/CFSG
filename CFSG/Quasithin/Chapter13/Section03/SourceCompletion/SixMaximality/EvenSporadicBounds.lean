module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds.Sporadic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Even and sporadic upper-component bounds for the A₆ source

An upper component whose order is divisible by 360 but not by 64 has only
the derived binary symplectic alternative among the rank-two models of
Theorem C. Its existing concrete equivalence identifies it with A₆.
The other even families have unipotent subgroups divisible by 64; the
small PSL₃(2) and G₂(2)′ exceptions fail the factor 360 condition.
The degree-four and degree-five binary linear rows also have a factor 64.

The reexported sporadic bounds use divisibility into |GL₅(2)| and the same
two-part constraint. These are the source model inspections for the
original A₆ maximality argument in 13.3.2, printed pp.884--885, using the
literal local carrier list of Theorem C, A.2.4, printed p.33.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds
open Chapter1.Section02.LocalModels
open Theory.SpecificGroups.SymplecticFour

variable {G : Type*} [Group G]

private theorem sixtyFour_dvd_binary_power {a b : ℕ} (h : 6 ≤ a * b) :
    64 ∣ (2 ^ a) ^ b := by
  change 2 ^ 6 ∣ (2 ^ a) ^ b
  rw [←pow_mul]
  exact Nat.pow_dvd_pow 2 h

private theorem not_linear_rank_two {f : ℕ} (hf : 1 ≤ f)
    (hlarge : 360 ∣ Nat.card G) (hsmall : ¬64 ∣ Nat.card G)
    (hm : ClassicalGroup.IsPSL G 3 (2 ^ f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotent,hF,←Nat.card_congr e.toEquiv] at hd
  have hf1 : f = 1 := by
    by_contra hn
    exact hsmall ((sixtyFour_dvd_binary_power (by omega : 6 ≤ f * 3)).trans hd)
  have hc : Nat.card G = 168 := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hf1]
    norm_num
  exact (by decide : ¬360 ∣ 168) (hc ▸ hlarge)

private theorem not_symplectic_rank_two {f : ℕ} (hf : 2 ≤ f)
    (hsmall : ¬64 ∣ Nat.card G) (hm : ClassicalGroup.IsPSp G 2 (2 ^ f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let a := e.trans (EvenProjective.equiv (F := F)).symm
  apply hsmall
  rw [Nat.card_congr a.toEquiv,card_sp,hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (sixtyFour_dvd_binary_power (by omega : 6 ≤ f * 4)) _) _

private theorem not_g2_rank_two {f : ℕ} (hf : 2 ≤ f)
    (hsmall : ¬64 ∣ Nat.card G) (hm : ClassificationModels.IsG2At G (2 ^ f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (sixtyFour_dvd_binary_power (by omega : 6 ≤ f * 6)) _) _

private theorem not_triality_rank_two {f : ℕ} (hf : 1 ≤ f)
    (hsmall : ¬64 ∣ Nat.card G)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f (by omega)).mp hm
  let P := Triality.Standard.binaryParameters f (by omega : 0 < f)
  have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
  change (2 ^ f) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier f _) at hd
  rw [←Nat.card_congr e.toEquiv] at hd
  exact hsmall ((sixtyFour_dvd_binary_power (by omega : 6 ≤ f * 12)).trans hd)

private theorem not_ree_rank_two (m : ℕ) (hsmall : ¬64 ∣ Nat.card G)
    (hm : IsReeF4At G m) : False := by
  obtain ⟨d,⟨e⟩⟩ := hm
  let a := e.trans d.modelEquiv
  have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent,←Nat.card_congr a.toEquiv] at hd
  exact hsmall ((sixtyFour_dvd_binary_power (by omega : 6 ≤ (2 * m + 1) * 12)).trans hd)

/-- The only literal rank-two Theorem C carrier with the original A₆
divisor and source two-part bound is A₆ itself. -/
theorem rankTwo_alternatingSix
    (hlarge : 360 ∣ Nat.card G) (hsmall : ¬64 ∣ Nat.card G)
    (hm : RankTwoTheoremC G) : IsAlternating G 6 := by
  cases hm with
  | linear f hf he => exact (not_linear_rank_two hf hlarge hsmall he).elim
  | symplectic f hf he => exact (not_symplectic_rank_two hf hsmall he).elim
  | g2 f hf he => exact (not_g2_rank_two hf hsmall he).elim
  | triality f hf he => exact (not_triality_rank_two hf hsmall he).elim
  | ree m _ he => exact (not_ree_rank_two m hsmall he).elim
  | symplectic_derived he =>
    obtain ⟨e⟩ := he
    exact ⟨e.trans Binary.projectiveDerivedEquivAlternatingSix⟩
  | g2_derived he =>
    obtain ⟨e⟩ := he
    have hc : Nat.card G = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
    exact ((by decide : ¬360 ∣ 6048) (hc ▸ hlarge)).elim
  | tits he =>
    obtain ⟨e⟩ := he
    apply (hsmall _).elim
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card]
    norm_num

/-- Both binary linear rows of Theorem C exceed the source two-part bound. -/
theorem binary_linear_excluded (hsmall : ¬64 ∣ Nat.card G)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL G n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc]
    decide
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc]
    decide

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds
