module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedAction
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Models
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import Theory.GroupTheory.SimpleSectionOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Small constrained rows and the degree-five binary row

The actual action with soluble kernel forces the marked simple section's
order to divide the component's core-central quotient order. Orders at
most 20160 and the order of PSL5(2) exclude precisely the remaining finite
star rows for the unitary and Suzuki markings.

Source: Aschbacher--Smith C.2.7 and 4.2.12--13, pp.146--147,610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

theorem unitary_card_not_dvd_linear_five_two {S : Type*} [Group S]
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU S 3 (2 ^ s)) :
    ¬ Nat.card S ∣ 9999360 := by
  obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
  rw [Nat.card_congr e.toEquiv,
    HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
      J hcard hconj]
  intro hd
  have hle := Nat.le_of_dvd (by decide : 0 < 9999360) hd
  have hs3 : s ≤ 3 := by
    by_contra hh
    have hq : 16 ≤ 2 ^ s := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 4 ≤ s)
    have hn := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 3) 1)
        (Nat.pow_le_pow_left hq 3)) (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have hden : Nat.gcd 3 (2 ^ s + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hb := (Nat.div_le_div_right hn (c := 3)).trans
      (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
    norm_num at hb
    omega
  interval_cases s <;> norm_num at hd

theorem suzuki_card_not_dvd_linear_five_two {S : Type*} [Group S]
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* SuzukiMatrixGroup m) :
    ¬ Nat.card S ∣ 9999360 := by
  rw [Nat.card_congr e.toEquiv,suzukiMatrixGroup_card m (by omega)]
  intro hd
  have hle := Nat.le_of_dvd (by decide : 0 < 9999360) hd
  have hm1 : m ≤ 1 := by
    by_contra hh
    have hq : 32 ≤ 2 ^ (2*m+1) :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 5 ≤ 2*m+1)
    have hb := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.pow_le_pow_left hq 2)) (Nat.sub_le_sub_right hq 1)
    norm_num at hb
    omega
  have he : m = 1 := by omega
  norm_num [he] at hd

variable {G S : Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]
variable {H M F R W : Subgroup G}

theorem constrained_normalized_simple_order_dvd
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H) :
    Nat.card S ∣ Nat.card (coreCentralQuotient K) := by
  obtain ⟨r,hker,_⟩ := constrained_normalized_inner_representation h hn K hK hq hout
  let := hker
  exact SimpleSection.card_dvd_of_solvable_representation hS π hπ r

theorem no_constrained_normalized_small_star
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    (hsize : 20160 < Nat.card S)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hsmall : Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) ≤ 20160) : False := by
  have hd := constrained_normalized_simple_order_dvd h hn hS π hπ K hK hq hout
  rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv] at hd
  have hd' := hd.trans (center (starImage (K.map H.subtype) R (K.map H.subtype))).card_quotient_dvd_card
  have hh := Nat.le_of_dvd (Nat.card_pos) hd'
  omega

theorem no_constrained_normalized_linear_five_two
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    (hsize : ¬ Nat.card S ∣ 9999360)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) : False := by
  have hd := constrained_normalized_simple_order_dvd h hn hS π hπ K hK hq hout
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans
    (QuotientGroup.congr _ _ e (FixedElementary.map_center e))
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
    Fin.prod_univ_zero,mul_one] at hc
  rw [Nat.card_congr ec.toEquiv,hc] at hd
  exact hsize hd
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

end
