module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Radical
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Defs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# A maximum-elementary offender for the actual component representation

The source factorization R = O₂(LR) O₂(Y_L) identifies the action image of
LR on W_L with that of L: O₂(LR) fixes W_L and O₂(Y_L) lies in L. We
construct this quotient map and identify its kernel with C_LR(W_L).

The earlier identities put the normal elementary subgroup W_L inside R
and force J(R) to act nontrivially. The maximum-elementary-subgroup bound
therefore supplies an offender for the centralizer quotient. Faithfulness
of the specified SL₃(2) action identifies its actor with the component
image, and the explicit linear equivalence from W_L.subgroupOf(LR) to
W_L intertwines both conjugation actions. Thus the offender belongs to
the precise representation used by the extension argument.

This argument applies with all five C.1.34 alternatives still available;
it does not require a moving-layer classification or any case exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
printed pp.75–76; C.1.34, pp.136–137; 15.3.16(2) and the factorization
in the first paragraph of 15.3.23, pp.1126,1128.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
  [(actionKernel d L).Normal]

private theorem plusImage_join_le
    (hfactor : d.R = (L ⊔ d.R).pCoreIn 2 ⊔ (YL d L).pCoreIn 2)
    (hfix : (L ⊔ d.R).pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G)) :
    plusImage d L (L ⊔ d.R) ≤ plusImage d L L := by
  have hL : L ≤ overgroup d L := le_sup_left.trans le_sup_left
  have hR : d.R ≤ overgroup d L := le_sup_right.trans le_sup_left
  have hK : (L ⊔ d.R).pCoreIn 2 ≤ overgroup d L :=
    ((L ⊔ d.R).pCoreIn_le 2).trans le_sup_left
  have hY : (YL d L).pCoreIn 2 ≤ L := ((YL d L).pCoreIn_le 2).trans
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right)
  have hzero : plusImage d L ((L ⊔ d.R).pCoreIn 2) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hfix hx)
  unfold plusImage
  rw [subgroupOf_sup hL hR, Subgroup.map_sup]
  apply sup_le le_rfl
  conv_lhs => rw [hfactor]
  rw [subgroupOf_sup hK (hY.trans hL), Subgroup.map_sup]
  exact sup_le (hzero.le.trans bot_le) (map_mono (comap_mono hY))

private def joinActionMap
    (himage : plusImage d L (L ⊔ d.R) ≤ plusImage d L L) :
    (L ⊔ d.R : Subgroup G) →* plusImage d L L :=
  ((plusMap d L).comp (inclusion le_sup_left)).codRestrict _ fun g =>
    himage (mem_map.mpr ⟨inclusion le_sup_left g, g.property, rfl⟩)

private theorem joinActionMap_surjective
    (himage : plusImage d L (L ⊔ d.R) ≤ plusImage d L L) :
    Function.Surjective (joinActionMap d L himage) := by
  intro x
  obtain ⟨l, rfl⟩ := componentMap_surjective d L x
  exact ⟨inclusion le_sup_left l, rfl⟩

private theorem joinActionMap_ker
    (himage : plusImage d L (L ⊔ d.R) ≤ plusImage d L L)
    (hW : d.componentSpan L ≤ L ⊔ d.R) :
    (joinActionMap d L himage).ker =
      centralizer ((d.componentSpan L).subgroupOf (L ⊔ d.R) : Set (L ⊔ d.R : Subgroup G)) := by
  ext g
  change (joinActionMap d L himage g = 1) ↔ _
  constructor
  · intro h w hw
    have he : plusMap d L (inclusion le_sup_left g) = 1 := congrArg Subtype.val h
    have hc := (QuotientGroup.eq_one_iff _).mp he
    exact Subtype.ext (hc w hw)
  · intro h
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    intro w hw
    exact congrArg Subtype.val (h ⟨w, hW hw⟩ hw)


/-- The exact component representation is FF, from the earlier radical identities. -/
theorem componentRepresentation_isFFModule [Finite G]
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : L.pCoreIn 2 ≤ d.R)
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M)
    (hJR : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (L ⊔ d.R).pCoreIn 2 ⊔ (YL d L).pCoreIn 2) :
    IsFFModule (componentRepresentation d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e) := by
  classical
  have hcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R := le_sup_left.trans hfactor.ge
  have hWR : d.componentSpan L ≤ d.R := span_le_radical d L hR hN hcore
  have hW : d.componentSpan L ≤ L ⊔ d.R := hWR.trans le_sup_right
  have himage := plusImage_join_le d L hfactor
    (LR_core_centralizes_span d L hcore (hR.le.trans inf_le_right))
  -- Work inside LR: normality here is relative, not ambient normality.
  let H := L ⊔ d.R
  let W := (d.componentSpan L).subgroupOf H
  let _ : W.Normal := (normal_subgroupOf_iff_le_normalizer hW).mpr
    ((le_sup_left : H ≤ overgroup d L).trans hN)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hW
  let q := joinActionMap d L himage
  have hq := joinActionMap_surjective d L himage
  have hk := joinActionMap_ker d L himage hW
  let ρ := Representation.NormalElementaryQuotient.representation W q hq hk
  -- Transport the actual Thompson subgroup through the subgroup inclusion.
  have hj : ¬ Stellmacher.elementaryAbelianMaxJ (d.R.subgroupOf H) ≤ q.ker := by
    intro h
    apply thompson_not_centralizes_span d L houtside hC hJR
    have hm : Stellmacher.elementaryAbelianMaxJ d.R =
        (Stellmacher.elementaryAbelianMaxJ (d.R.subgroupOf H)).map H.subtype := by
      rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ H.subtype_injective,
        map_subgroupOf_eq_of_le (show d.R ≤ H from le_sup_right)]
    rw [hm]
    rintro _ ⟨x, hx, rfl⟩
    have he : plusMap d L (inclusion le_sup_left x) = 1 := congrArg Subtype.val (h hx)
    have hc : inclusion (show H ≤ overgroup d L from le_sup_left) x ∈ actionKernel d L :=
      (QuotientGroup.eq_one_iff _).mp he
    exact hc
  have hFF : IsFFModule ρ :=
    Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le W q hq hk
      (d.R.subgroupOf H) (comap_mono hWR) hj
  -- Faithfulness identifies the marked matrix group with the component image.
  let hc := core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)
  let f : SL →* plusImage d L L := (coreQuotientMap d L hc).comp e.symm.toMonoidHom
  have hf : Function.Bijective f := by
    refine ⟨?_, (coreQuotientMap_surjective d L hc).comp e.symm.surjective⟩
    intro x y hxy
    apply componentRepresentation_injective d L hN hc e houtside hC
    change representation d hN ((f x : plusImage d L L) : Plus d L) =
      representation d hN ((f y : plusImage d L L) : Plus d L)
    rw [hxy]
  let F : SL ≃* plusImage d L L := MulEquiv.ofBijective f hf
  -- Identify the two span carriers and check the actions on lifts from L.
  let E : Additive W ≃ₗ[ZMod 2] Additive (d.componentSpan L) :=
    LinearEquiv.ofBijective
      ((subgroupOfEquivOfLe hW).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hW).bijective
  apply hFF.map_equivariant ρ (componentRepresentation d L hN hc e)
    F.symm.toMonoidHom F.symm.injective E
  intro x v
  obtain ⟨l, rfl⟩ := componentMap_surjective d L x
  have he : F.symm (componentMap d L l) = e (QuotientGroup.mk l) := by
    apply F.injective
    rw [F.apply_symm_apply]
    change componentMap d L l = coreQuotientMap d L hc (e.symm (e (QuotientGroup.mk l)))
    rw [e.symm_apply_apply]
    rfl
  change E (ρ (componentMap d L l) v) = componentRepresentation d L hN hc e
    (F.symm (componentMap d L l)) (E v)
  rw [he]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((ρ (q (inclusion le_sup_left l)) v).toMul : H) : G) = _
  rw [componentRepresentation_apply]
  exact congrArg H.subtype (Representation.NormalElementaryQuotient.representation_apply
    W q hq hk (inclusion le_sup_left l) v)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
