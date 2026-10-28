module
public import Theory.Alternating.FivePairBorel
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SymmetricFive.WreathComponents

/-!
# Recognizing the full wreath group from its residual and overlap

A six-group overgroup of an ambient Sylow subgroup meets a normal A₅ pair
in a subgroup with normal Sylow two-subgroup. Its two-core therefore has
order divisible by sixteen. If its two-core quotient is S₃ wr C₂, the
ambient order is divisible by 128; the residual also contributes 3600.
Their least common multiple is the full order 28800 of S₅ wr C₂. Thus any
faithful embedding into that wreath group is onto.

All residual, overlap and Sylow inclusions refer to the same ambient group.
Source: Aschbacher--Smith 10.2.3(3), printed p.745, using E.2.2(1).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

open Subgroup Theory.GroupTheory
local notation "A" => alternatingGroup (Fin 5)

private theorem pair_six_core_divisor {X : Type*} [Group X] [Finite X]
    (R : Subgroup X) [R.Normal] (e : R ≃* (A × A))
    (S : Sylow 2 X) (M : Subgroup X)
    (hM : IsPGroup 6 M) (hSM : (S : Subgroup X) ≤ M) :
    16 ∣ Nat.card (pCore 2 M) := by
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_normal R
  let P := M.subgroupOf R
  have hQP : (Q : Subgroup R) ≤ P := by
    rw [hQ]
    intro x hx
    exact hSM hx
  let Qe := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn := Theory.AlternatingFive.pair_six_overgroup_le_sylow_normalizer Qe
    (P.map e.toMonoidHom) (hM.comap_subtype.map e.toMonoidHom) (map_mono hQP)
  have hQemap : (Qe : Subgroup (A × A)) = (Q : Subgroup R).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hPN : P ≤ normalizer (Q : Set R) := by
    have hn' : P.map e.toMonoidHom ≤
        normalizer ((Q : Subgroup R).map e.toMonoidHom : Set (A × A)) := by
      rw [← hQemap]
      exact hn
    rw [← map_normalizer_eq_of_bijective _ e.bijective] at hn'
    exact (map_le_map_iff_of_injective e.injective).mp hn'
  let QP := Q.subtype hQP
  have hQPn : (QP : Subgroup P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQP).mpr hPN
  have hcore : pCore 2 P = (QP : Subgroup P) :=
    le_antisymm (pCore_isPGroup.le_sylow_of_normal QP) (le_sSup ⟨hQPn,QP.isPGroup'⟩)
  have hQcard : Nat.card Q = 16 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) (K := (Q : Subgroup R)) e.injective]
    change Nat.card Qe = 16
    rw [Qe.card_eq_multiplicity, Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hPcard : Nat.card (pCore 2 P) = 16 := by
    rw [hcore,Sylow.coe_subtype,Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv]
    exact hQcard
  let N := R.subgroupOf M
  let ePN : P ≃* N := {
    toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun := fun y => ⟨⟨y.val.val,y.property⟩,y.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hNcard : Nat.card (pCore 2 N) = 16 := by
    rw [← hPcard]
    exact (Nat.card_congr ((ePN.subgroupMap (pCore 2 P)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 ePN))).toEquiv).symm
  have hle : (pCore 2 N).map N.subtype ≤ pCore 2 M :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map N.subtype⟩
  have hd := card_dvd_of_le hle
  rwa [card_map_of_injective N.subtype_injective,hNcard] at hd

local notation "W" => Theory.SpecificGroups.SymmetricFive.WreathComponents.W

/-- The actual pair residual and maximal overlap force a faithful wreath map to be onto. -/
theorem wreath_of_pair_and_overlap {X : Type*} [Group X] [Finite X]
    (e : pResidual 2 X ≃* (A × A)) (S : Sylow 2 X) (M : Subgroup X)
    (hM : IsPGroup 6 M) (hSM : (S : Subgroup X) ≤ M)
    (heM : Nonempty ((M ⧸ pCore 2 M) ≃* WreathTwoResidual.Actor))
    (a : X →* W) (ha : Function.Injective a) : Nonempty (X ≃* W) := by
  have h16 := pair_six_core_divisor (pResidual 2 X) e S M hM hSM
  have h72 : Nat.card (M ⧸ pCore 2 M) = 72 := by
    obtain ⟨b⟩ := heM
    rw [Nat.card_congr b.toEquiv]
    change Nat.card (RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2))) = 72
    rw [RegularWreathProduct.card]
    have h : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [h]
    norm_num [Nat.card_eq_fintype_card]
  have h1152 : 1152 ∣ Nat.card M := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),h72]
    exact Nat.mul_dvd_mul (dvd_refl 72) h16
  have h128 : 128 ∣ Nat.card X :=
    (show 128 ∣ 1152 by decide).trans (h1152.trans (card_subgroup_dvd_card M))
  have h3600 : 3600 ∣ Nat.card X := by
    have hr : Nat.card (pResidual 2 X) = 3600 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
    exact hr ▸ card_subgroup_dvd_card (pResidual 2 X)
  have hd : 28800 ∣ Nat.card X := by
    have hh := Nat.lcm_dvd h128 h3600
    norm_num [Nat.lcm] at hh
    exact hh
  have hw : Nat.card W = 28800 := by
    norm_num [Theory.SpecificGroups.SymmetricFive.WreathComponents.W,
      Theory.SpecificGroups.SymmetricFive.WreathComponents.Sym,
      Theory.SpecificGroups.SymmetricFive.WreathComponents.C2,RegularWreathProduct.card,
      Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hc : Nat.card X = Nat.card W := by
    apply Nat.le_antisymm (Nat.card_le_card_of_injective a ha)
    rw [hw]
    exact Nat.le_of_dvd Nat.card_pos hd
  exact ⟨MulEquiv.ofBijective a ((Nat.bijective_iff_injective_and_card a).mpr ⟨ha,hc⟩)⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
