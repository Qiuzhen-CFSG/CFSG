module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Sixty-four as an upper bound for the binary moving group

For any elementary binary SL3(2) action, an involution with fixed index at
most four has displacement rank at most two. The checked three-conjugate
generation bound puts the entire moving subspace in dimension at most six.
Translation through the subgroup/subspace correspondence gives order at
most sixty-four without faithfulness, irreducibility or a splitting premise.

Source: the elementary three-involution argument used in MS93 (1993),
pp.842--843, applied to the complete quotient in (4.5.4)(iv), p.899.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]

private abbrev subgroupSpace : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

private theorem moving_space_eq (ρ : SL →* MulAut E) :
    subgroupSpace (commutatorAction ρ.range E) = Coinvariants.ker (Offenders.linearize ρ) := by
  apply le_antisymm
  · change commutatorAction ρ.range E ≤
      (Coinvariants.ker (Offenders.linearize ρ)).toAddSubgroup.toSubgroup'
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨a, g, rfl⟩, v, rfl⟩
    change -Additive.ofMul v + Offenders.linearize ρ g (Additive.ofMul v) ∈
      Coinvariants.ker (Offenders.linearize ρ)
    simpa only [sub_eq_add_neg, add_comm] using
      Coinvariants.sub_mem_ker (ρ := Offenders.linearize ρ) g (Additive.ofMul v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change ρ g v.toMul / v.toMul ∈ commutatorAction ρ.range E
    rw [div_eq_mul_inv, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨ρ g, g, rfl⟩, v.toMul, mul_comm _ _⟩

private theorem small_fixedCodim_four [Finite E] (ρ : SL →* MulAut E) (t : SL)
    (hsmall : Nat.card (commutatorAction (zpowers (ρ t)) E) ≤ 4) :
    fixedCodim (Offenders.linearize ρ) (zpowers t) ≤ 2 := by
  let C := commutatorAction (zpowers (ρ t)) E
  have hc : 2 ^ Module.finrank (ZMod 2) (subgroupSpace C) ≤ 2 ^ 2 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subgroupSpace C)
    rw [Nat.card_zmod] at he
    rw [← he]
    exact hsmall
  have hd : Module.finrank (ZMod 2) (subgroupSpace C) ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [fixedCodim_zpowers_eq_displacement_rank]
  apply (Submodule.finrank_mono (t := subgroupSpace C) ?_).trans hd
  rintro _ ⟨v, rfl⟩
  change ρ t v.toMul / v.toMul ∈ commutatorAction (zpowers (ρ t)) E
  rw [div_eq_mul_inv, commutatorAction_eq_closure]
  exact Subgroup.subset_closure ⟨⟨ρ t, mem_zpowers (ρ t)⟩, v.toMul, mul_comm _ _⟩

/-- Three conjugate involutions bound the moving order by sixty-four.
Faithfulness or a splitting hypothesis is unnecessary. -/
theorem moving_card_le_sixtyFour [Finite E] (ρ : SL →* MulAut E) (t : SL)
    (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hsmall : (FixedPoints.subgroup (zpowers (ρ t)) E).index ≤ 4) :
    Nat.card (commutatorAction ρ.range E) ≤ 64 := by
  have ht' : (ρ t)^2 = 1 := by rw [← map_pow,ht,map_one]
  have hd := (MulAut.involution_fixed_displacement_card_data (ρ t) ht').1
  have hi := (FixedPoints.subgroup (zpowers (ρ t)) E).card_mul_index
  have hpos : 0 < Nat.card (FixedPoints.subgroup (zpowers (ρ t)) E) := Nat.card_pos
  have hsmall' : Nat.card (commutatorAction (zpowers (ρ t)) E) ≤ 4 := by nlinarith
  have hf := small_fixedCodim_four ρ t hsmall'
  have hb := ModuleAlternatives.Models.commutator_finrank_le_three_mul (Offenders.linearize ρ) t ht hne
  have hdim : Module.finrank (ZMod 2) (Coinvariants.ker (Offenders.linearize ρ)) ≤ 6 := by omega
  change Nat.card (subgroupSpace (commutatorAction ρ.range E)) ≤ 64
  rw [moving_space_eq,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
