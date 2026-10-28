module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalGeometry
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionConsequences
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.OrbitControl
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.InnerAction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneOrbit
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourMixedPlane
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Complete
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNatural
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianAmbient
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianResidual
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianLift
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNormalizer
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixed
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryFixed
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryAmalgam
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianWhole
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianExchanged
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianPointWhole
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFixedLine
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituents
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentQuotient

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCompletion

/-!
# Assembly of the natural branch of 12.9

The original point span is abelian in both source degrees, four and five.
The component proofs exclude the normal and larger-center nonabelian cases.
In the remaining fixed-line case, they construct a moved component and its
actual homogeneous constituent. The marked branch has multiplicity two;
self-duality, the original seven-section and the actor bound exclude its
remaining carriers. The exchanged branch is excluded using the original
Lagrangian dimension identity, point-centralizer bound and square form.

On this same flag, local control and weak closure give Sylow hyperplane
control. The binary inner action constructs the actual S₃ overgroup and
moving conjugate, yielding TerminalConfiguration as an output.
`naturalBranchInput_of_modules` assembles these results without a constituent
or catalogue premise. It retains the genuine earlier module theorem and all
original hypotheses, including the independently supplied NaturalReduction 4.
The existing general conditional assembly interfaces remain available.

Source: Aschbacher--Smith, G.11.6--9 and 12.9.1--9, printed
pp.365--369,857--864; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u

/-- Assemble the independently proved stages without adding hypotheses to
NaturalBranchInput. Its four arguments remain obligations of the source owner. -/
theorem naturalBranchInput_of_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (fusion : FusionInput K) (terminal : TerminalInput K) : NaturalBranchInput K := by
  intro X _ _ T L V n h hn preferred earlier four
  obtain ⟨_, F, _⟩ := h.exists_flag_geometry earlier.structural
  obtain ⟨hab, ⟨C⟩⟩ := components X T L V n h hn preferred earlier four F
  have hc := localControl X T L V n h hn preferred earlier F hab C
  have hf := fusion X T L V n h hn earlier F hab C hc
  exact ⟨F, hab, hf.hyperplanes, terminal X T L V n h hn earlier F hab C hc hf⟩

/-- Apply the existing terminal contradiction to the four completed source
stages. This is conditional until all four arguments have been discharged. -/
theorem contradiction_of_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (fusion : FusionInput K) (terminal : TerminalInput K)
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (preferred : PreferredDimension K T n) (earlier : EarlierSetupResults K)
    (four : NaturalReduction K 4) : False :=
  natural_branch_contradiction
    (naturalBranchInput_of_stages components localControl fusion terminal)
    earlier four h hn preferred

/-- Assemble the remaining source obligations; the hyperplane clause and
weak-closure normalizer bound are supplied by the proved fusion deductions. -/
theorem naturalBranchInput_of_weakClosure_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (weakClosure : WeakClosureInput K) (terminal : TerminalInput K) : NaturalBranchInput K :=
  naturalBranchInput_of_stages components localControl
    (fusionInput_of_weakClosure weakClosure) terminal

/-- Apply the completed terminal construction to the actual local component.
Only the S₃ overgroup selection remains in the terminal stage; the other three
arguments still require their source proofs. -/
theorem contradiction_of_symmetric_three_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (weakClosure : WeakClosureInput K) (overgroups : SymmetricThreeOvergroupInput K)
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (preferred : PreferredDimension K T n) (earlier : EarlierSetupResults K)
    (four : NaturalReduction K 4) : False := by
  obtain ⟨_, F, _⟩ := h.exists_flag_geometry earlier.structural
  obtain ⟨hab, ⟨C⟩⟩ := components G T L V n h hn preferred earlier four F
  have hc := localControl G T L V n h hn preferred earlier F hab C
  have hf := fusionInput_of_weakClosure weakClosure G T L V n h hn earlier F hab C hc
  obtain ⟨H, ht, hHK, he, hout⟩ := overgroups G T L V n h hn earlier F hab C hc
  exact contradiction_of_symmetric_three_overgroup h hn earlier F hab hc.normalizers hf
    H ht (hHK.trans hc.overgroup.2.1) he hout

/-- The unchanged natural-branch contract, with the terminal construction reduced
to cubic Sylow overgroup selection. The A₇ selection is already proved; its
binary linear counterparts and the preceding three stages remain with this owner. -/
theorem naturalBranchInput_of_cubic_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (weakClosure : WeakClosureInput K) (overgroups : CubicOvergroupInput K) :
    NaturalBranchInput K :=
  naturalBranchInput_of_weakClosure_stages components localControl weakClosure
    (terminalInput_of_cubicOvergroups overgroups)

/-- The terminal stages are reduced to the literal binary inner-action premise.
The component, local-control, weak-closure and inner-action proofs remain here. -/
theorem naturalBranchInput_of_inner_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (weakClosure : WeakClosureInput K) (inner : BinaryInnerActionInput K) :
    NaturalBranchInput K :=
  naturalBranchInput_of_cubic_stages components localControl weakClosure
    (cubicOvergroupInput_of_inner inner)

/-- Apply the completed source 12.9.9 family in the actual natural-branch
consumer. Only component/abelianity, local control and binary innerness remain;
no weak-closure, hyperplane or core-action callback is required. -/
theorem naturalBranchInput_of_local_inner_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K)
    (inner : BinaryInnerActionInput K) : NaturalBranchInput K :=
  naturalBranchInput_of_inner_stages components localControl (weakClosureInput K) inner

/-- Apply the completed fusion and terminal families to the unchanged source
contract. The component/abelianity and local-control arguments remain with
this assembly owner; there is no remaining inner-action premise. -/
theorem naturalBranchInput_of_local_stages {K : GroupClass.{u}}
    (components : ComponentInput K) (localControl : LocalControlInput K) :
    NaturalBranchInput K :=
  naturalBranchInput_of_local_inner_stages components localControl (binaryInnerActionInput K)

/-- Apply the complete component geometry to the unchanged natural-branch
consumer. Nonnormal abelianity and local control remain with this source
assembly owner; fusion and the actual terminal configuration are proved. -/
theorem naturalBranchInput_of_nonnormal_abelian_local_stages
    (abelian : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X) (n : ℕ),
      HigherRankHypothesis KnownSimple.IsKnownSimple T L V n → n = 4 ∨ n = 5 →
      PreferredDimension KnownSimple.IsKnownSimple T n →
      EarlierSetupResults.{u} KnownSimple.IsKnownSimple →
      NaturalReduction KnownSimple.IsKnownSimple.{u} 4 →
      ∀ F : InvariantFlag T V n, ¬ ((F.Li L 1).subgroupOf F.H).Normal →
        IsMulCommutative F.U)
    (localControl : LocalControlInput KnownSimple.IsKnownSimple.{u}) :
    NaturalBranchInput KnownSimple.IsKnownSimple.{u} :=
  naturalBranchInput_of_local_stages (componentInput_of_nonnormal_abelian abelian) localControl

/-- Apply the degree-five catalogue exclusion to the completed fusion and
terminal construction. Construction of the catalogue witness and the
original local-control input remain obligations of this source owner. -/
theorem contradiction_of_five_corrected_catalogue
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀)
    (localControl : LocalControlInput KnownSimple.IsKnownSimple.{u}) : False := by
  have hab := Components.five_point_span_abelian_of_corrected_catalogue h earlier F B v W X X₀ hc
  obtain ⟨C⟩ := Components.componentGeometry earlier h (Or.inr rfl) F
  have preferred : PreferredDimension KnownSimple.IsKnownSimple T 5 := by
    intro he
    omega
  have control := localControl G T L V 5 h (Or.inr rfl) preferred earlier F hab C
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    G T L V 5 h (Or.inr rfl) earlier F hab C control
  obtain ⟨d⟩ := terminalInput_of_cubicOvergroups
    (cubicOvergroupInput_of_inner (binaryInnerActionInput KnownSimple.IsKnownSimple))
    G T L V 5 h (Or.inr rfl) earlier F hab C control fusion
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab fusion.hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index

/-- Apply the completed nonabelian sieve to the original natural-branch
assembly. The remaining mathematical premises are catalogue construction,
the degree-four orthogonal contradiction, and original local control. The
orthogonal owner retains the preferred-dimension and natural-reduction
inputs; all other rows, including A₇, are eliminated here. -/
theorem naturalBranchInput_of_catalogue_orthogonal_local_stages
    (catalogue : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X) (n : ℕ),
      (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) → n = 4 ∨ n = 5 →
      (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) →
      ∀ (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U),
        let := Components.nonabelian_hat_elementary h earlier F hne
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
          (W : Submodule (ZMod 2) (Additive F.Uhat))
          (A : Subgroup F.TerminalHdot) (A₀ : Subgroup A),
          ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
            F.terminalRepresentation B v W A A₀)
    (orthogonal : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X),
      (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4) →
      PreferredDimension KnownSimple.IsKnownSimple T 4 →
      (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) →
      NaturalReduction KnownSimple.IsKnownSimple.{u} 4 →
      ∀ (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U),
        let := Components.nonabelian_hat_elementary h earlier F hne
        ∀ (g : X), g ∈ F.P L → g ∉ F.H →
        ∀ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
          ChapterG.Section11.CaseFive F.terminalRepresentation B → False)
    (localControl : LocalControlInput KnownSimple.IsKnownSimple.{u}) :
    NaturalBranchInput KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ T L V n h hn preferred earlier four
  obtain ⟨_,F,_,_,_,_,g,hgP,hgH⟩ := h.exists_flag_geometry earlier.structural
  have hab : IsMulCommutative F.U := by
    by_contra hne
    let := Components.nonabelian_hat_elementary h earlier F hne
    obtain ⟨B,v,W,A,A₀,hc⟩ := catalogue X T L V n h hn earlier F hne
    obtain ⟨rfl,h5⟩ := Components.nonabelian_corrected_catalogue_orthogonal
      h hn earlier F hne g hgP hgH B v W A A₀ hc
    exact orthogonal X T L V h preferred earlier four F hne g hgP hgH B h5
  obtain ⟨C⟩ := Components.componentGeometry earlier h hn F
  have control := localControl X T L V n h hn preferred earlier F hab C
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    X T L V n h hn earlier F hab C control
  exact ⟨F,hab,fusion.hyperplanes,terminalInput_of_cubicOvergroups
    (cubicOvergroupInput_of_inner (binaryInnerActionInput KnownSimple.IsKnownSimple))
    X T L V n h hn earlier F hab C control fusion⟩

/-- The original CaseFive contradiction discharges the orthogonal branch.
The corrected catalogue and the local-control stage remain explicit, with
the genuine earlier module theorem and natural reduction retained. -/
theorem naturalBranchInput_of_modules_catalogue_local_stages
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (catalogue : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X) (n : ℕ),
      (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) → n = 4 ∨ n = 5 →
      (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) →
      ∀ (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U),
        let := Components.nonabelian_hat_elementary h earlier F hne
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
          (W : Submodule (ZMod 2) (Additive F.Uhat))
          (A : Subgroup F.TerminalHdot) (A₀ : Subgroup A),
          ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
            F.terminalRepresentation B v W A A₀)
    (localControl : LocalControlInput KnownSimple.IsKnownSimple.{u}) :
    NaturalBranchInput KnownSimple.IsKnownSimple.{u} := by
  apply naturalBranchInput_of_catalogue_orthogonal_local_stages catalogue ?_ localControl
  intro X _ _ T L V h preferred earlier four F hne
  let := Components.nonabelian_hat_elementary h earlier F hne
  dsimp only
  intro g hgP hgH B h5
  exact Components.nonabelian_caseFive_impossible modules h preferred earlier four
    F hne g hgP hgH B h5

/-- The actual degree-five fusion and terminal configuration, constructed on
the original flag from abelianity alone. The local-control premises are proved. -/
theorem five_hyperplanes_and_terminal_of_abelian
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) :
    SylowHyperplaneControl T L V ∧ Nonempty (TerminalConfiguration F L) := by
  obtain ⟨C⟩ := Components.componentGeometry earlier h (Or.inr rfl) F
  have control := five_localControl_of_abelian h earlier F hab C
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    G T L V 5 h (Or.inr rfl) earlier F hab C control
  exact ⟨fusion.hyperplanes,terminalInput KnownSimple.IsKnownSimple
    G T L V 5 h (Or.inr rfl) earlier F hab C control fusion⟩

/-- Complete the abelian degree-five branch with the actual terminal witness. -/
theorem five_abelian_contradiction
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) : False := by
  obtain ⟨hyperplanes,⟨d⟩⟩ := five_hyperplanes_and_terminal_of_abelian h earlier F hab
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index

/-- The original degree-five source argument now needs only construction of
the corrected nonabelian catalogue witness; its local-control stage is proved. -/
theorem five_contradiction_of_corrected_catalogue
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (A : Subgroup F.TerminalHdot) (A₀ : Subgroup A)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W A A₀) : False :=
  five_abelian_contradiction h earlier F
    (Components.five_point_span_abelian_of_corrected_catalogue h earlier F B v W A A₀ hc)

/-- In the original degree-four PSL₄(2) point row, local control supplies
both hyperplane control and the actual terminal configuration on the same flag. -/
theorem four_binary_four_hyperplanes_and_terminal
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2) :
    SylowHyperplaneControl T L V ∧ Nonempty (TerminalConfiguration F L) := by
  have control := four_localControl_of_binary_four h earlier F hab C hm
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    G T L V 4 h (Or.inl rfl) earlier F hab C control
  exact ⟨fusion.hyperplanes,terminalInput KnownSimple.IsKnownSimple
    G T L V 4 h (Or.inl rfl) earlier F hab C control fusion⟩

/-- The original abelian degree-four branch is impossible in the PSL₄(2) point row. -/
theorem four_binary_four_abelian_contradiction
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2) : False := by
  obtain ⟨hyperplanes,⟨d⟩⟩ := four_binary_four_hyperplanes_and_terminal h earlier F hab C hm
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index

/-- In the original degree-four mixed PSL₅(2) point row, local control supplies
both hyperplane control and the actual terminal configuration on the same flag. -/
theorem four_binary_five_hyperplanes_and_terminal
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    SylowHyperplaneControl T L V ∧ Nonempty (TerminalConfiguration F L) := by
  have control := four_localControl_of_binary_five h earlier F hab C hm
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    G T L V 4 h (Or.inl rfl) earlier F hab C control
  exact ⟨fusion.hyperplanes,terminalInput KnownSimple.IsKnownSimple
    G T L V 4 h (Or.inl rfl) earlier F hab C control fusion⟩

/-- The original abelian degree-four branch is impossible in the mixed PSL₅(2) point row. -/
theorem four_binary_five_abelian_contradiction
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) : False := by
  obtain ⟨hyperplanes,⟨d⟩⟩ := four_binary_five_hyperplanes_and_terminal h earlier F hab C hm
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index


/-- The complete fusion and terminal construction in both source degrees,
on the same original flag. All local-control premises are discharged. -/
theorem hyperplanes_and_terminal_of_abelian
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) :
    SylowHyperplaneControl T L V ∧ Nonempty (TerminalConfiguration F L) := by
  obtain ⟨C⟩ := Components.componentGeometry earlier h hn F
  have control := localControl_of_abelian h hn earlier F hab C
  have fusion := fusionInput_of_weakClosure (weakClosureInput KnownSimple.IsKnownSimple)
    G T L V n h hn earlier F hab C control
  exact ⟨fusion.hyperplanes,terminalInput KnownSimple.IsKnownSimple
    G T L V n h hn earlier F hab C control fusion⟩

/-- The original natural-module branch is impossible whenever its original
point span is abelian. This covers both degrees and every point-model row. -/
theorem abelian_contradiction
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) : False := by
  obtain ⟨hyperplanes,⟨d⟩⟩ := hyperplanes_and_terminal_of_abelian h hn earlier F hab
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index

/-- General assembly through a supplied corrected nonabelian catalogue.
The specialized original-hypothesis assembly below constructs the natural
branch directly while retaining the earlier module theorem and reduction. -/
theorem naturalBranchInput_of_modules_catalogue
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (catalogue : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X) (n : ℕ),
      (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) → n = 4 ∨ n = 5 →
      (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) →
      ∀ (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U),
        let := Components.nonabelian_hat_elementary h earlier F hne
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
          (W : Submodule (ZMod 2) (Additive F.Uhat))
          (A : Subgroup F.TerminalHdot) (A₀ : Subgroup A),
          ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
            F.terminalRepresentation B v W A A₀) :
    NaturalBranchInput KnownSimple.IsKnownSimple.{u} :=
  naturalBranchInput_of_modules_catalogue_local_stages modules catalogue localControlInput


/-- The original natural branch in both degrees, retaining the genuine earlier
module theorem. The invariant flag, abelian point span, hyperplane control and
terminal configuration are constructed, with no catalogue premise. -/
theorem naturalBranchInput_of_modules
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple) :
    NaturalBranchInput KnownSimple.IsKnownSimple.{u} := by
  intro G _ _ T L V n h hn preferred earlier four
  obtain ⟨_,F,_,_,_,_,g,hgP,hgH⟩ := h.exists_flag_geometry earlier.structural
  have hab := Components.point_span_abelian_of_original modules h hn preferred earlier four
    F g hgP hgH
  obtain ⟨hyperplanes,terminal⟩ := hyperplanes_and_terminal_of_abelian h hn earlier F hab
  exact ⟨F,hab,hyperplanes,terminal⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
