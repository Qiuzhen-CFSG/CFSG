module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SuzukiPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates

/-!
# Full Suzuki endpoint markings from the original source factors

The original F.1.1 Suzuki quotient identifies the canonical root-generated
group and its root Sylow. SuzukiPanelCompletion extends this to the entire
faithful endpoint quotient, pins the root by one inner conjugation, and
identifies the full Borel with the standard root normalizer. The original
factor map agrees with the given factor quotient marking under that same
conjugation: the whole-root cover identifies both representatives modulo
its radical, which is contained in the full panel kernel.

Transport through the original endpoint equivalence preserves the actual
core of the whole Borel and the literal quotient square on every endpoint
element. The previously conditional Ree coordinate constructor then gives
both root parameters, their multiplication, their matrix projection and
exact image under the original endpoint map. All Suzuki parameters occur,
including zero. The truncated order-ten factor uses its proved order-twenty
root cover and gives the same binary full-panel coordinates.

The marking, split quotient and original F.1.1 hypotheses remain unchanged.
No full-panel model, Borel marking, original-factor perfectness or Weyl order
is an additional premise. This discharges the Suzuki marking consumed by
(6H) and Section 10; the linear marking, row selection and remaining mixed
relations are separate source obligations.

Source: Fong--Seitz I (3B), (5C), (6H), pp.13,25--26,51 and II §10,
pp.221--230; DGS, Groups and Graphs (1985), Theorem D, p.224;
Aschbacher--Smith F.1.1--3. The Chapter 12 application is in
SuzukiPanelApplications.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SuzukiPanel
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
include e h split μ

/-- The given original factor marking extends to the whole faithful panel
up to the single inner conjugation used to pin its canonical root. -/
theorem marked_panel_factor_compatible :
    ∃ (g : SuzukiMatrixGroup m)
      (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m),
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = SuzukiRootSubgroup m ∧
      ∀ a : L i, σ (QuotientGroup.mk' (panelKernel Q i)
        (MarkedLocal.factorInEndpoint Q e i a)) =
          g * μ (QuotientGroup.mk' (pCore 2 (L i)) a) * g⁻¹ := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := MarkedLocal.suzuki_remainder_le_kernel_all Q e h split i T hT μ
  have hc := MarkedLocal.suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ
  let α := MarkedLocal.regularFactorRootEquiv Q e h split i T hT hV hc
  obtain ⟨g,σ,hsigma,hroot,hB⟩ := PanelCompletion.exists_suzuki_panel_marking Q split i hV
    (α.trans μ)
    (HexagonStructure.originalSuzukiAllRootEquiv Q e h split i T hT μ)
  refine ⟨g,σ,hB,hroot,?_⟩
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
  change g * μ (α r) * g⁻¹ = _
  rw [show α r = QuotientGroup.mk' (pCore 2 (L i)) a from α.apply_symm_apply _]

/-- An original Suzuki quotient constructs a marking of the ENTIRE faithful
endpoint quotient, with its full Borel and canonical root. -/
theorem marked_panel :
    ∃ σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m,
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = SuzukiRootSubgroup m := by
  obtain ⟨_,σ,hB,hroot,_⟩ := marked_panel_factor_compatible Q e h split i μ
  exact ⟨σ,hB,hroot⟩

/-- The same full-panel marking on the original endpoint keeps its literal
core quotient and endpoint map, including the entire original Borel. -/
theorem original_panel :
    ∃ (g : SuzukiMatrixGroup m) (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
      (τ : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
        SuzukiMatrixGroup m),
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (∀ x : parabolic L S i,
        τ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := L) (S := S) i) x) =
          σ (QuotientGroup.mk' (panelKernel Q i) (MarkedLocal.endpoint Q e i x))) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = SuzukiRootSubgroup m ∧
      ∀ l : L i, τ (QuotientGroup.mk'
        (ReeSource.originalPanelKernel (L := L) (S := S) i)
        ⟨l,(show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) l.property⟩) =
          g * μ (QuotientGroup.mk' (pCore 2 (L i)) l) * g⁻¹ := by
  obtain ⟨g,σ,hB,hroot,hfactor⟩ := marked_panel_factor_compatible Q e h split i μ
  let a := ReeSource.originalPanelQuotientEquiv Q e h i
  let τ := a.trans σ
  refine ⟨g,σ,τ,hB,?_,?_,hroot,?_⟩
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

/-- Construct the original two-parameter root charts required in (6H) and
Section 10 from the original factor alone. All model and Borel premises of
the existing coordinate constructor have been discharged. -/
theorem original_coordinates :
    ∃ (τ : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
        SuzukiMatrixGroup m)
      (u : BinaryGaloisField (2*m+1) → BinaryGaloisField (2*m+1) → parabolic L S i),
      (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (∀ a b c d, u a b * u c d = u (a+c) (b+d+a*suzukiTits m c)) ∧
      (∀ a b, τ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := L) (S := S) i)
        (u a b)) = (matrixRootPoint m a b : SuzukiMatrixGroup m)) ∧
      Set.range (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) =>
        MarkedLocal.endpointMap Q e i (u p.1 p.2)) =
          (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  obtain ⟨_,σ,τ,hB,hτ,hsquare,_,_⟩ := original_panel Q e h split i μ
  let u := ReeSource.originalSuzukiParameter Q e split i m σ hB
  refine ⟨τ,u,hτ,ReeSource.originalSuzukiParameter_mul Q e split i m σ hB,?_,
    ReeSource.originalSuzukiParameter_range Q e split i m σ hB⟩
  intro a b
  rw [hsquare]
  exact ReeSource.originalSuzukiParameter_projection Q e h split i m σ hB a b

omit μ in
/-- The truncated dihedral F.1.1 factor has full faithful panel Sz(2),
using its already proved order-twenty root cover. -/
theorem marked_dihedral_panel
    (μD : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) :
    ∃ σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0,
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = SuzukiRootSubgroup 0 := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  obtain ⟨_,σ,_,hroot,hB⟩ := PanelCompletion.exists_suzuki_panel_marking Q split i
    (MarkedLocal.dihedral_remainder_le_kernel Q e h split i T hT μD)
    (MarkedLocal.dihedralSuzukiRankOneEquiv Q e h split i T hT μD)
    (HexagonStructure.originalDihedralRootEquiv Q e h split i T hT μD)
  exact ⟨σ,hB,hroot⟩

omit μ in
/-- The original order-ten factor supplies the same binary source chart;
its order-twenty full panel, entire Borel and original core are retained. -/
theorem dihedral_original_coordinates
    (μD : ((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) :
    ∃ (τ : (parabolic L S i ⧸ ReeSource.originalPanelKernel (L := L) (S := S) i) ≃*
        SuzukiMatrixGroup 0)
      (u : BinaryGaloisField 1 → BinaryGaloisField 1 → parabolic L S i),
      (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map τ.toMonoidHom =
        normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)) ∧
      (∀ a b c d, u a b * u c d = u (a+c) (b+d+a*suzukiTits 0 c)) ∧
      (∀ a b, τ (QuotientGroup.mk' (ReeSource.originalPanelKernel (L := L) (S := S) i)
        (u a b)) = (matrixRootPoint 0 a b : SuzukiMatrixGroup 0)) ∧
      Set.range (fun p : BinaryGaloisField 1 × BinaryGaloisField 1 =>
        MarkedLocal.endpointMap Q e i (u p.1 p.2)) =
          (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  obtain ⟨σ,hB,_⟩ := marked_dihedral_panel Q e h split i μD
  let τ := (ReeSource.originalPanelQuotientEquiv Q e h i).trans σ
  let u := ReeSource.originalSuzukiParameter Q e split i 0 σ hB
  refine ⟨τ,u,?_,ReeSource.originalSuzukiParameter_mul Q e split i 0 σ hB,
    ReeSource.originalSuzukiParameter_projection Q e h split i 0 σ hB,
    ReeSource.originalSuzukiParameter_range Q e split i 0 σ hB⟩
  change (ReeSource.originalFaithfulBorel (L := L) (S := S) i).map
    (σ.toMonoidHom.comp (ReeSource.originalPanelQuotientEquiv Q e h i).toMonoidHom) = _
  rw [←map_map,ReeSource.originalPanelQuotientEquiv_borel]
  exact hB

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SuzukiPanel
