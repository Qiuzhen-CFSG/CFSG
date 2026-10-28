module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerCubic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer

/-!
# Baumann control of the extraspecial residual centralizer

For the original abelian flag, the orbit W = ⟨V₁^C⟩ is reduced in C R₁
and its faithful action has order prime to three. The three-free FF theorem
therefore makes J(R₁) centralize W. The exact seed centralizer is O₂(C R₁):
its full centralizer lies in H, and the literal residual action confines
C ∩ H to L₁ O₂(H). Baumann heredity now identifies Baum(R₁) with
Baum(O₂(C R₁)), putting C inside N_G(L).

No normality of C R₁ in N_G(K) is needed. All action kernels and subgroup
intersections are those of the original group and flag.

Source: Aschbacher–Smith, proof of 14.7.21(1), printed p.1050.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

private theorem thompson_centralizes_reduced_three_free_action
    {X : Type u} [Group X] [Finite X]
    (W : Subgroup X) (hr : IsPReduced 2 W)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hthree : Nat.Coprime 3 (centralizer (W : Set X)).index) :
    elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (W : Set X) := by
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (W : Set X))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (X ⧸ centralizer (W : Set X)) := {
    Cover := X
    kernel := centralizer (W : Set X)
    sqtk := hsq
    equiv := MulEquiv.refl _ }
  have hn := ChapterB.SourceInduction.no_ff_of_three_free (ρ := ρ)
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
    hr.quotient_pCore_eq_bot c hthree
  by_contra hJ
  exact hn (NormalElementaryQuotient.isFFModule_of_thompson_not_le W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (S : Subgroup X)
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    (by simpa only [q,QuotientGroup.ker_mk'] using hJ))

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_normalizer_thompson_centralizes_seed
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    elementaryAbelianMaxJ (F.Ri L 1) ≤
      centralizer (conjugateSpanBy (F.Vi 1) (normalizerResidualCentralizer F) : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let X := C ⊔ F.Ri L 1
  let W := conjugateSpanBy (F.Vi 1) C
  obtain ⟨hw,hwQ,hwC,hr,hLC,hthree⟩ :=
    extraspecial_normalizer_central_seed_reduced d h hab structural previous faithful earlier he
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXN : X ≤ N := hXY.trans inf_le_left
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hS' : (S : Subgroup X) = (F.Ri L 1).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hZX : F.Vi 1 ≤ X := by
    have hz : F.Vi 1 ≤ F.Ri L 1 := le_pCoreIn_of_normalizes
      (by let := h.chosen.elementary
          let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
          exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
    exact hz.trans le_sup_right
  have hWX : W ≤ X := conjugateSpanBy_le hZX
    ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hsq : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXN)).mp
      ((d.qtke.twoLocal_sqtk
        (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1.1).subgroup
          (X.subgroupOf N))
  have hindex : Nat.Coprime 3 (centralizer (W.subgroupOf X : Set X)).index := by
    rw [← relIndex_top_right,← relIndex_map_map_of_injective
      (centralizer (W.subgroupOf X : Set X)) ⊤ X.subtype_injective,
      map_centralizer_subtype,map_subgroupOf_eq_of_le hWX,
      ←MonoidHom.range_eq_map,range_subtype,inf_relIndex_left]
    exact hthree
  have hh := thompson_centralizes_reduced_three_free_action (W.subgroupOf X) hr hsq S hindex
  have hm := map_mono (f := X.subtype) hh
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hS,
    map_centralizer_subtype,map_subgroupOf_eq_of_le hWX] at hm
  exact hm.trans inf_le_right

private theorem normalizer_action_on_star (n : F.H)
    (x : (K F) ⧸ pCore 2 (K F)) :
    residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) x) =
      MulAut.conjNormal (starMap F n) (residualStarEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H k =>
    change residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) (QuotientGroup.mk' _ k)) = _
    apply Subtype.ext
    rw [pCoreNormalizerAction_mk,residualStarEquiv_mk]
    change starMap F _ = starMap F n *
      (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) * (starMap F n)⁻¹
    rw [residualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
    congr 1


theorem extraspecial_normalizer_centralizer_inter_H
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ⊓ F.H ≤ F.Li L 1 ⊔ F.H.pCoreIn 2 := by
  obtain ⟨e⟩ := he
  have hs := point_star_eq_center_of_extraspecial_residual h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  let P := pResidual 2 (HStar F.H)
  intro x hx
  let xH : F.H := ⟨x,hx.2⟩
  have hact : pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) xH) = 1 := by
    obtain ⟨n,hn,hnx⟩ := hx.1
    have hn' : n = inclusion (H_normalizes_K F) xH := Subtype.ext hnx
    exact hn' ▸ hn
  have hc : starMap F xH ∈ centralizer (P : Set (HStar F.H)) := by
    intro y hy
    obtain ⟨z,hz⟩ := (residualStarEquiv F).surjective (⟨y,hy⟩ : P)
    have hfix := normalizer_action_on_star xH z
    rw [hact] at hfix
    have hfix' : starMap F xH * y * (starMap F xH)⁻¹ = y := by
      have hh := congrArg Subtype.val hfix.symm
      change starMap F xH * (residualStarEquiv F z : HStar F.H) *
        (starMap F xH)⁻¹ = (residualStarEquiv F z : HStar F.H) at hh
      simpa only [hz] using hh
    exact (mul_inv_eq_iff_eq_mul.mp hfix').symm
  have hp : starMap F xH ∈ P :=
    centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2) hc
  have hz : starMap F xH ∈ star F (F.Li L 1) := by
    rw [hs]
    refine ⟨⟨starMap F xH,hp⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y y.property)
  have hl : xH ∈ ((F.Li L 1).subgroupOf F.H) ⊔ pCore 2 F.H := by
    have hm : xH ∈ ((star F (F.Li L 1)).comap (starMap F)) := hz
    simpa only [CriticalFusion.Source.star,comap_map_eq,starMap,QuotientGroup.ker_mk'] using hm
  have hh := mem_map_of_mem F.H.subtype hl
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hLH] at hh

/-- The source seed centralizer in R₁ is exactly the two-core of C R₁. -/
theorem extraspecial_normalizer_seed_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let C := normalizerResidualCentralizer F
    let X := C ⊔ F.Ri L 1
    let W := conjugateSpanBy (F.Vi 1) C
    F.Ri L 1 ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let X := C ⊔ R
  let W := conjugateSpanBy (F.Vi 1) C
  let D := X ⊓ centralizer (W : Set G)
  let Q := R ⊓ centralizer (W : Set G)
  have hRH : R ≤ F.H := (pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXC : X ≤ normalizer (C : Set G) :=
    (hXY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  have hRT : R ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hspan : conjugateSpanBy (F.Vi 1) X = W :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (hRT.trans (F.invariant 1))
      (le_sup_right.trans hXC)
  have hXW : X ≤ normalizer (W : Set G) := hspan ▸ le_normalizer_conjugateSpanBy _ _
  have hXD : X ≤ normalizer (D : Set G) :=
    (le_inf X.le_normalizer (hXW.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hDH : D ≤ F.H := inf_le_right.trans
    ((centralizer_le (le_conjugateSpanBy _ _)).trans (Subgroup.centralizer_le_normalizer _))
  have hDpoint : D ≤ F.Li L 1 ⊔ R := by
    have hprod : (X : Set G) = (R : Set G) * (C : Set G) := by
      rw [show X = R ⊔ C from sup_comm C R]
      exact coe_mul_of_left_le_normalizer_right _ _ (le_sup_right.trans hXC)
    intro x hx
    obtain ⟨r,hr,c,hc,heq⟩ := hprod ▸ hx.1
    have hcH : c ∈ F.H := by
      have hh := F.H.mul_mem (F.H.inv_mem (hRH hr)) (hDH hx)
      simpa only [←heq,inv_mul_cancel_left] using hh
    have hcL := extraspecial_normalizer_centralizer_inter_H h hab structural previous he ⟨hc,hcH⟩
    exact heq ▸ (F.Li L 1 ⊔ R).mul_mem (mem_sup_right hr)
      ((sup_le_sup_left core_le_point_core _) hcL)
  have hpointR : F.Li L 1 ⊔ R ≤ normalizer (R : Set G) :=
    (sup_le le_sup_left (pCoreIn_le 2 _)).trans
      ((F.Li L 1 ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hDQ : D ≤ normalizer (Q : Set G) :=
    (le_inf (hDpoint.trans hpointR)
      (inf_le_right.trans (centralizer (W : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  have hQX : Q ≤ X.pCoreIn 2 :=
    (le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G))).to_le inf_le_left)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right) hDQ).trans
      (pCoreIn_mono_of_normalizes inf_le_left hXD)
  obtain ⟨_,_,_,hr,_,_⟩ := extraspecial_normalizer_central_seed_reduced
    d h hab structural previous faithful earlier he
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hXR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  have hWX : W ≤ X := by
    have hZR : F.Vi 1 ≤ R := le_pCoreIn_of_normalizes
      (by let := h.chosen.elementary
          let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
          exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
    exact conjugateSpanBy_le (hZR.trans le_sup_right)
      ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hXCW : X.pCoreIn 2 ≤ centralizer (W : Set G) := by
    have hh := map_mono (f := X.subtype) (le_centralizer_iff.mp hr.le_centralizer_pCore)
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWX] at hh
    exact hh.trans inf_le_right
  exact le_antisymm hQX (le_inf hXR hXCW)

/-- Baumann heredity for the actual source seed orbit. -/
theorem extraspecial_normalizer_baumann_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ChapterB.baumann (F.Ri L 1) =
      ChapterB.baumann ((normalizerResidualCentralizer F ⊔ F.Ri L 1).pCoreIn 2) := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let X := C ⊔ R
  let W := conjugateSpanBy (F.Vi 1) C
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hQR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  obtain ⟨hw,_,_,hr,_,_⟩ := extraspecial_normalizer_central_seed_reduced
    d h hab structural previous faithful earlier he
  let : IsElementaryAbelian 2 W := hw
  have hZR : F.Vi 1 ≤ R := le_pCoreIn_of_normalizes
    (by let := h.chosen.elementary
        let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
        exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hWX : W ≤ X := conjugateSpanBy_le (hZR.trans le_sup_right)
    ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hWQ : W ≤ X.pCoreIn 2 := by
    have hh : (W.subgroupOf X).map X.subtype ≤ X.pCoreIn 2 :=
      map_mono (f := X.subtype) hr.le_pCore
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hJ : elementaryAbelianMaxJ R ≤ centralizer (W : Set G) :=
    extraspecial_normalizer_thompson_centralizes_seed d h hab structural previous faithful earlier he
  have hWZ := elementary_centralizer_maxJ_le_omegaCenter R W (hWQ.trans hQR)
    (le_centralizer_iff.mp hJ)
  have hBQ : ChapterB.baumann R ≤ X.pCoreIn 2 := by
    rw [← extraspecial_normalizer_seed_centralizer d h hab structural previous faithful earlier he]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hWZ))
  exact (baumann_eq_of_intermediate R (X.pCoreIn 2) hBQ hQR).symm

/-- The literal residual-quotient centralizer lies in the original L-normalizer. -/
theorem extraspecial_normalizer_centralizer_le_M
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ≤ normalizer (L : Set G) := by
  apply le_trans ?_ (extraspecial_baumann_normalizer d h hab structural previous earlier he)
  rw [extraspecial_normalizer_baumann_core d h hab structural previous faithful earlier he]
  let X := normalizerResidualCentralizer F ⊔ F.Ri L 1
  exact (show normalizerResidualCentralizer F ≤ X from le_sup_left).trans
    ((X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (normalizer_le_normalizer_baumann _))
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
