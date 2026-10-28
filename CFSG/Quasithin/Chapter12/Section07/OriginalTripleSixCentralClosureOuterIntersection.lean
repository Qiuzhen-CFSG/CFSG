module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterModel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterRank
import Theory.Representation.HexacodeAction.OddPointQuotient
import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The original outer closure meets the chosen module in order sixteen

The full original H-action kernel contains W and has an original U-image
of order four. This bounds U intersect W from above. The same marked odd
involution acts on the whole original U; its displacement and scalar point
bound the U-image in the actual quotient H/W by four, giving the reverse
bound. No involution lift or additional core equality is assumed.

Source: Aschbacher--Smith12.7.17 and the conclusion of12.7.20,
printed pp.845--846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem odd_closure_quotient_card_le_four (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (H W : Subgroup G) (hUH : U ≤ H) (hWH : W ≤ H)
    [(W.subgroupOf H).Normal]
    (hVW : tripleSixPoint D a z ≤ W)
    (f : Automizer U →* HexAutomorphisms)
    (hchart : ∀ (b : Automizer U) (u : U),
      (tripleSixPointCoordinates D a (b.val u)).toAdd =
        Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd)
    (g : HexAutomorphisms) (hg : g ∈ (inducedAutomizer U W).map f)
    (hodd : hexSign g = -1) (h2 : g ^ 2 = 1)
    (hgz : Hexacode.action g (tripleSixPointCoordinates D a z).toAdd =
      (tripleSixPointCoordinates D a z).toAdd) :
    Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' (W.subgroupOf H))) ≤ 4 := by
  let q := QuotientGroup.mk' (W.subgroupOf H)
  let A := (U.subgroupOf H).map q
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  let := D.elementary
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  let b : Multiplicative hexacode →* A :=
    (q.subgroupMap (U.subgroupOf H)).comp
      (((subgroupOfEquivOfLe hUH).symm.toMonoidHom).comp c.symm.toMonoidHom)
  let ℓ : hexacode →ₗ[ZMod 2] Additive A := b.toAdditiveRight.toZModLinearMap 2
  have hbc (u : U) : (b (c u)).val = q ⟨u, hUH u.property⟩ := by
    change q ((subgroupOfEquivOfLe hUH).symm (c.symm (c u))).val = _
    rw [c.symm_apply_apply]
    rfl
  have hℓ : Function.Surjective ℓ :=
    (q.subgroupMap_surjective (U.subgroupOf H)).comp
      ((subgroupOfEquivOfLe hUH).symm.surjective.comp c.symm.surjective)
  let E := ℓ.ker
  have hmem (w : hexacode) : w ∈ E ↔
      (⟨(c.symm (Multiplicative.ofAdd w) : G),
        hUH (c.symm (Multiplicative.ofAdd w)).property⟩ : H) ∈ W.subgroupOf H := by
    change b (Multiplicative.ofAdd w) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hPE : (Submodule.span Hexacode.F {v}).restrictScalars (ZMod 2) ≤ E := by
    intro w hw
    apply (hmem w).mpr
    apply hVW
    refine ⟨c.symm (Multiplicative.ofAdd w), ?_, rfl⟩
    change (c (c.symm (Multiplicative.ofAdd w))).toAdd ∈ Submodule.span Hexacode.F {v}
    rw [c.apply_symm_apply]
    change w ∈ Submodule.span Hexacode.F {v} at hw ⊢
    exact hw
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hg
  have hmove (x : hexacode) :
      Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) x - x ∈ E := by
    let u := c.symm (Multiplicative.ofAdd x)
    let wH : H := ⟨w, hWH hw⟩
    let uH : H := ⟨u, hUH u.property⟩
    have hwN : wH ∈ W.subgroupOf H := hw
    have hqw : q wH = 1 := (QuotientGroup.eq_one_iff wH).mpr hwN
    have hu : c u = Multiplicative.ofAdd x := c.apply_symm_apply _
    have hcu : c ((U.normalizerMonoidHom.rangeRestrict w).val u) =
        Multiplicative.ofAdd (Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) x) := by
      apply Multiplicative.toAdd.injective
      have hh := hchart (U.normalizerMonoidHom.rangeRestrict w) u
      change (c ((U.normalizerMonoidHom.rangeRestrict w).val u)).toAdd =
        Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) (c u).toAdd at hh
      rw [hu] at hh
      exact hh
    change ℓ (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    change b (Multiplicative.ofAdd _) = b (Multiplicative.ofAdd x)
    rw [← hcu, ← hu]
    apply Subtype.ext
    rw [hbc, hbc]
    change q (wH * uH * wH⁻¹) = q uH
    rw [map_mul, map_mul, map_inv, hqw, one_mul, inv_one, mul_one]
  have hv : v ≠ 0 := by
    intro he
    exact hz (c.injective (show c z = c 1 from he.trans c.map_one.symm))
  have hd := Hexacode.odd_involution_point_quotient_finrank_le_two
    (f (U.normalizerMonoidHom.rangeRestrict w)) hodd h2 v hv hgz E hPE hmove
  rw [(ℓ.quotKerEquivOfSurjective hℓ).finrank_eq] at hd
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  change Nat.card A = (Nat.card (ZMod 2)) ^ Module.finrank (ZMod 2) (Additive A) at hc
  rw [Nat.card_zmod] at hc
  exact hc.trans_le (Nat.pow_le_pow_right (by decide) hd)

/-- The literal original outer closure meets the unchanged chosen module
in an elementary subgroup of order sixteen. -/
theorem original_tripleSix_central_closure_outer_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    Nat.card (U ⊓ W : Subgroup G) = 16 := by
  let C := centralizer ({(z : G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let I := U ⊓ W
  let U₀ := U.subgroupOf H
  let W₀ := W.subgroupOf H
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  change H ≤ C ∧ W = conjugateSpanBy V1 H ∧ W ≤ H.pCoreIn 2 ∧
    (frattini W).map W.subtype ≤ zpowers (z : G) ∧
    ⁅W,H.pCoreIn 2⁆ ≤ zpowers (z : G) ∧ ¬ U ≤ H.pCoreIn 2 ∧
    ¬ ⁅U,W⁆ ≤ zpowers (z : G) at hc
  have hWH : W ≤ H := hc.2.2.1.trans (pCoreIn_le 2 H)
  have hUH : U ≤ H := D.le_sylow.trans le_sup_right
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [hc.2.1]
    exact le_normalizer_conjugateSpanBy _ _
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hHW
  let := D.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUH
  have hUc : Nat.card U₀ = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).trans
      ((Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card)
  have hIc : Nat.card (U₀ ⊓ W₀ : Subgroup H) = Nat.card I :=
    Nat.card_congr (subgroupOfEquivOfLe (show I ≤ H from inf_le_left.trans hUH)).toEquiv
  obtain ⟨N,hN,hmem,_,_,_,_,_,_,_,hcase⟩ :=
    original_tripleSix_central_closure_outer_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hfour : Nat.card (U₀.map (QuotientGroup.mk' N)) = 4 :=
    hcase.resolve_left houter
  have hWN : W₀ ≤ N := by
    intro w hw
    apply (hmem w).mpr
    intro u hu
    exact hc.2.2.2.2.1 (commutator_mem_commutator hu (hc.2.2.1 hw))
  have hNc : Nat.card (U₀ ⊓ N : Subgroup H) = 16 := by
    have hm := IsElementaryAbelian.card_inf_ker_mul_card_map U₀ (QuotientGroup.mk' N)
    rw [QuotientGroup.ker_mk',hfour,hUc] at hm
    omega
  have hupper : Nat.card I ≤ 16 := by
    have hh := card_le_of_le (inf_le_inf_left U₀ hWN)
    rwa [hIc,hNc] at hh
  obtain ⟨_,f,_,_,_,hchart,_,e,_,_,heven,hprod⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  let v := (tripleSixPointCoordinates D a z).toAdd
  let B := ((inducedAutomizer U W).map f).subgroupOf (Hexacode.fullVectorStabilizer v)
  have hswap : (Equiv.swap 0 1,1) ∈ B.map e.toMonoidHom := by
    rw [show B.map e.toMonoidHom = productCore from hprod]
    exact ⟨mem_top _,one_mem _⟩
  obtain ⟨g,hg,hgmark⟩ := hswap
  have hgodd : hexSign g.val = -1 := by
    rcases Int.units_eq_one_or (hexSign g.val) with he | he
    · have hh := (heven g).mp he
      rw [show e g = (Equiv.swap 0 1,1) from hgmark] at hh
      exact ((by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) hh).elim
    · exact he
  have hg2 : g.val ^ 2 = 1 := by
    have hh : g ^ 2 = 1 := by
      apply e.injective
      rw [map_pow,show e g = (Equiv.swap 0 1,1) from hgmark,map_one]
      decide
    exact congrArg Subtype.val hh
  have hbound : Nat.card (U₀.map (QuotientGroup.mk' W₀)) ≤ 4 :=
    odd_closure_quotient_card_le_four D a z hz H W hUH hWH
      (le_conjugateSpanBy V1 R) f hchart g.val hg hgodd hg2 g.property
  have hm := IsElementaryAbelian.card_inf_ker_mul_card_map U₀ (QuotientGroup.mk' W₀)
  rw [QuotientGroup.ker_mk',hIc,hUc] at hm
  have hlo := Nat.mul_le_mul_left (Nat.card I) hbound
  rw [hm] at hlo
  change Nat.card I = 16
  omega

end CFSG.Quasithin.Chapter12.Section07

