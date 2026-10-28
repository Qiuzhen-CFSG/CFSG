module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeStableLineLifts
public import Theory.GroupAction.ElementaryTwoTernaryLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicContainment
/-!
# Irreducibility of the original extraspecial Sylow action

A stable proper subgroup of the literal extraspecial Frattini quotient
lifts to two T-normalized, two-perfect cubic subgroups generating K.
The selected critical actor gives each Sylow overgroup its actual S₃
quotient. Normal-point cubic containment places both lifts in N_G(L),
contradicting H's escape. Thus T* acts irreducibly on K*/Φ(K*).

An elementary two-actor on a ternary plane always preserves a cubic
line, so T* is not elementary. All original quotient maps and intrinsic
cubic kernels are retained; no local-recognition premise is introduced.
Source: Aschbacher–Smith, 14.7.9 and 14.7.15(2), printed pp.1045,1047.
The remaining point-core structure and the order-sixteen interval still
require proof before 14.7.20 and the residual classification can close.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal star Sylow acts irreducibly on the extraspecial Frattini quotient. -/
theorem extraspecial_star_sylow_frattini_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (J : Subgroup ((pResidual 2 (HStar F.H)) ⧸ frattini (pResidual 2 (HStar F.H))))
    (hs : ∀ a : star F (T : Subgroup G), ∀ x ∈ J,
      quotientAut (frattini (pResidual 2 (HStar F.H)))
        (MulAut.conjNormal (a : HStar F.H)) x ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  by_contra! hnJ
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hk : IsPGroup 2 (starMap F).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨A,B,hAB,hA,hB⟩ := IsExtraspecial.exists_cubic_lifts_of_stable_frattini_line
    (starMap F) (QuotientGroup.mk'_surjective _) hk hP heP
    ((T : Subgroup G).subgroupOf F.H) T.isPGroup'.comap_subtype J hnJ.1 hnJ.2 hs
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have contained (A : Subgroup F.H) (hAK : A ≤ pResidual 2 F.H)
      (hperfect : IsPPerfect 2 A)
      (hAT : (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H))
      (hc : Nat.card (A.map (starMap F)) = 3)
      (hZ : A.map (starMap F) ≠ (center P).map P.subtype)
      (hker : ((starMap F).comp A.subtype).ker = pCore 2 A)
      (hquot : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map F.H.subtype ≤ normalizer (L : Set G) := by
    let Y := A.map F.H.subtype
    have hYH : Y ≤ F.H := map_subtype_le A
    let e : A ≃* Y := equivMapOfInjective A F.H.subtype F.H.subtype_injective
    have hstar : star F Y = A.map (starMap F) := by
      change ((A.map F.H.subtype).comap F.H.subtype).map (starMap F) = _
      rw [comap_map_eq_self_of_injective F.H.subtype_injective]
    have hYT : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
      rw [←map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      exact (map_mono hAT).trans (le_normalizer_map F.H.subtype)
    let f := (starMap F).comp (inclusion hYH)
    have hke : f.ker.comap e.toMonoidHom = pCore 2 A := hker
    have hkY : f.ker = pCore 2 Y := by
      calc
        f.ker = (f.ker.comap e.toMonoidHom).map e.toMonoidHom :=
          (map_comap_eq_self_of_surjective e.surjective _).symm
        _ = (pCore 2 A).map e.toMonoidHom := congrArg (map e.toMonoidHom) hke
        _ = pCore 2 Y := pCore_map_iso 2 e
    have hqY : Nat.card (Y ⧸ pCore 2 Y) = 3 :=
      (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hquot
    have he := extraspecial_cubic_sylow_quotient h hab structural previous hex hcard hexp
      Y hYH (map_mono hAK) hYT (hstar.symm ▸ hc) (hstar.symm ▸ hZ) hkY hqY
    exact cubic_containment_of_point_normal h hab structural previous faithful hn Y hYH
      (hperfect.of_surjective e.toMonoidHom e.surjective) hYT he
  have hAM := contained A (le_sup_left.trans_eq hAB) hA.1 hA.2.1 hA.2.2.1
    hA.2.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2
  have hBM := contained B (le_sup_right.trans_eq hAB) hB.1 hB.2.1 hB.2.2.1
    hB.2.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2
  apply h.flag_escape F previous
  rw [residual_product F]
  apply sup_le _ (h.sylow_normalizes structural)
  change (pResidual 2 F.H).map F.H.subtype ≤ _
  rw [←hAB,Subgroup.map_sup]
  exact sup_le hAM hBM

/-- The original star Sylow is not elementary: an elementary actor always
preserves a cubic line on the literal Frattini quotient. -/
theorem extraspecial_star_sylow_not_elementary
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ¬ IsElementaryAbelian 2 (star F (T : Subgroup G)) := by
  intro hel
  let := hel
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hE : Nat.card (P ⧸ frattini P) = 9 := by
    have hm := (frattini P).card_eq_card_quotient_mul_card_subgroup
    rw [IsExtraspecial.frattini_eq_center_three,IsExtraspecial.center_order_p 3 P,hP] at hm
    rw [IsExtraspecial.frattini_eq_center_three]
    omega
  let α : star F (T : Subgroup G) →* MulAut (P ⧸ frattini P) :=
    ((quotientAut (frattini P)).comp MulAut.conjNormal).comp
      (star F (T : Subgroup G)).subtype
  obtain ⟨J,hJ,hs⟩ := MulAut.exists_stable_three_of_elementary_two α hE
  rcases extraspecial_star_sylow_frattini_irreducible h hab structural previous faithful
      hex hcard hexp J hs with he | he
  · rw [he,card_bot] at hJ
    omega
  · rw [he,card_top,hE] at hJ
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
