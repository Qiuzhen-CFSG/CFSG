module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates

/-!
# Full linear endpoint markings from the original source factors

The original F.1.1 quotient Lᵢ/O₂(Lᵢ) identifies the whole root cover,
using linear (2B) and the equality of the canonical root and quotient-Sylow
orders. The Cartan completion theorem identifies the entire faithful
endpoint quotient with the same PSL₂, carrying the full Borel to a Sylow
normalizer. Comparing factor and root representatives modulo the cover
radical proves that this equivalence extends the original factor marking
exactly.

Transport through the original endpoint equivalence preserves the core of
the whole original Borel and its literal quotient square. The existing
ReeSource.linearRootEquiv then supplies injective additive coordinates on
the lifted original root, with the prescribed model projection and exact
image in the same source quotient. Neither endpoint perfectness nor a
Weyl-order condition is required; F₂ and both endpoint indices are included.

This discharges the full linear marking and Borel inputs of the Ree root
coordinates and Section 10 constructor. It does not select the octagonal
branch or prove its mixed equations. ReeFactorPanels combines it with the
checked Suzuki completion at that constructor; LinearPanelApplications
supplies the literal Chapter 12 applications.

Source: Fong--Seitz I (2B), (3B), (5C), pp.9,13,25--26, and II §10,
pp.221--222; DGS, Groups and Graphs (1985), Theorem D, p.224;
Aschbacher--Smith F.1.1--3, pp.259--260.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearPanel
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
include e h split μ

/-- The full faithful panel extends the original factor quotient marking exactly. -/
theorem marked_panel_factor_compatible :
    ∃ (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL(2,F))
      (T : Sylow 2 PSL(2,F)),
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (T : Set PSL(2,F)) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = (T : Subgroup PSL(2,F)) ∧
      ∀ a : L i, σ (QuotientGroup.mk' (panelKernel Q i)
        (MarkedLocal.factorInEndpoint Q e i a)) =
          μ (QuotientGroup.mk' (pCore 2 (L i)) a) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := MarkedLocal.linear_remainder_le_kernel Q e h split i T hT μ
  have hs : Nat.card (quotientSylow T) = Nat.card F :=
    (Nat.card_congr (MarkedLocal.linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (MarkedLocal.linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))
  have hc := (MarkedLocal.simpleRoot_card_linear Q e h split i T hT μ).trans hs.symm
  let α := MarkedLocal.regularFactorRootEquiv Q e h split i T hT hV hc
  obtain ⟨σ,Tm,hsigma,hroot,hB⟩ := PanelCompletion.exists_linear_panel_marking Q split i hV
    (α.trans μ)
  refine ⟨σ,Tm,hB,hroot,?_⟩
  intro a
  let r := α.symm (QuotientGroup.mk' (pCore 2 (L i)) a)
  have hr : RootLocalCover.coverEquiv Q split i hV r =
      QuotientGroup.mk' (LocalCover.radicalInClosure Q split i)
        (MarkedLocal.factorIntoClosure Q e h split i a) := by
    have he := MarkedLocal.regularFactorRootEquiv_cover Q e h split i T hT hV hc r
    change MarkedLocal.factorQuotientCoverEquiv Q e h split i T hT hV hc (α r) = _ at he
    rw [show α r = QuotientGroup.mk' (pCore 2 (L i)) a from α.apply_symm_apply _,
      MarkedLocal.factorQuotientCoverEquiv_mk] at he
    rw [RootLocalCover.coverEquiv_apply]
    exact he.symm
  rw [RootLocalCover.coverEquiv_apply] at hr
  have hd := QuotientGroup.eq.mp hr
  have hd' : (r : X ⧸ Q.D)⁻¹ * MarkedLocal.factorMap Q e i a ∈ localKernel Q i := by
    have hx := hd.2
    change ((inclusion (rankOne_le_localClosure Q split i) r : localClosure Q split i) : X ⧸ Q.D)⁻¹ *
      (MarkedLocal.factorIntoClosure Q e h split i a : X ⧸ Q.D) ∈ localKernel Q i at hx
    simpa only [Subgroup.coe_inclusion, MarkedLocal.factorIntoClosure_coe] using hx
  have he : PanelCompletion.rootPanelMap Q split i r =
      QuotientGroup.mk' (panelKernel Q i) (MarkedLocal.factorInEndpoint Q e i a) := by
    rw [PanelCompletion.rootPanelMap_apply]
    apply QuotientGroup.eq.mpr
    have hz : (inclusion (rankOne_le_parabolic Q split i) r)⁻¹ *
        MarkedLocal.factorInEndpoint Q e i a ∈ (localKernel Q i).subgroupOf (Endpoint Q i) := hd'
    simpa only [localKernel_subgroupOf, panelKernel, endpointBorel] using hz
  rw [←he,hsigma]
  change μ (α r) = _
  rw [show α r = QuotientGroup.mk' (pCore 2 (L i)) a from α.apply_symm_apply _]

/-- The same marking identifies the original whole-Borel core quotient and
keeps its literal square with the marked endpoint, at every field size. -/
theorem original_panel :
    ∃ (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL(2,F))
      (T : Sylow 2 PSL(2,F))
      (τ : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
        PSL(2,F)),
      (quotientBorel Q i).map σ.toMonoidHom = normalizer (T : Set PSL(2,F)) ∧
      (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (T : Set PSL(2,F)) ∧
      (∀ x : parabolic L S i,
        τ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := L) (S := S) i) x) =
          σ (QuotientGroup.mk' (panelKernel Q i) (MarkedLocal.endpoint Q e i x))) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = (T : Subgroup PSL(2,F)) ∧
      ∀ l : L i, τ (QuotientGroup.mk'
        (ReeSource.originalPanelKernel (L := L) (S := S) i)
        ⟨l,(show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) l.property⟩) =
          μ (QuotientGroup.mk' (pCore 2 (L i)) l) := by
  obtain ⟨σ,T,hB,hroot,hfactor⟩ := marked_panel_factor_compatible Q e h split i μ
  let a := ReeSource.originalPanelQuotientEquiv Q e h i
  let τ := a.trans σ
  refine ⟨σ,T,τ,hB,?_,?_,hroot,?_⟩
  · change (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map
      (σ.toMonoidHom.comp a.toMonoidHom) = _
    rw [←map_map,ReeSource.originalPanelQuotientEquiv_borel]
    exact hB
  · intro x
    exact congrArg σ (ReeSource.originalPanelQuotientEquiv_mk Q e h i x)
  · intro l
    change σ (a (QuotientGroup.mk' _ _)) = _
    rw [ReeSource.originalPanelQuotientEquiv_mk]
    exact hfactor l

/-- Construct the additive source chart on the original endpoint, including
its full-Borel marking, faithful projection and exact root image. -/
theorem original_coordinates :
    ∃ (τ : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
        PSL(2,F))
      (T : Sylow 2 PSL(2,F)) (u : Multiplicative F →* parabolic L S i),
      (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (T : Set PSL(2,F)) ∧
      Function.Injective u ∧
      (∀ a, τ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := L) (S := S) i)
        (u a)) = (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T a : PSL(2,F))) ∧
      ((MarkedLocal.endpointMap Q e i).comp u).range = simpleRoot Q split i := by
  obtain ⟨σ,T,τ,hB,hτ,hsquare,_,_⟩ := original_panel Q e h split i μ
  let a := (ReeSource.linearRootEquiv Q split i σ T hB).symm
  let u := (ReeSource.originalRootLift Q e split i).comp a.toMonoidHom
  refine ⟨τ,T,u,hτ,(ReeSource.originalRootLift_injective Q e split i).comp a.injective,?_,?_⟩
  · intro z
    rw [hsquare]
    have he := ReeSource.originalRootProjection_commutes Q e h split i (a z)
    rw [ReeSource.originalRootProjection,MonoidHom.comp_apply,
      ReeSource.originalPanelQuotientEquiv_mk] at he
    change σ (QuotientGroup.mk' (panelKernel Q i)
      (MarkedLocal.endpoint Q e i (ReeSource.originalRootLift Q e split i (a z)))) = _
    rw [he]
    exact ReeSource.linearParameter_projection Q split i σ T hB z
  · have he : (MarkedLocal.endpointMap Q e i).comp u =
        ReeSource.linearParameter Q split i σ T hB := by
      ext z
      exact ReeSource.originalRootLift_image Q e split i (a z)
    rw [he]
    exact ReeSource.linearParameter_range Q split i σ T hB

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearPanel
