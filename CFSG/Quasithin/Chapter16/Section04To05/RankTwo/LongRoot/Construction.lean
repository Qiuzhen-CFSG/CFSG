module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.OnanInput
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Construction.ScalarRecovery
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.OnanImageBounds

/-!
# The source application of an intrinsic root calculation

For X = modifiedCentralizerResidual L u, an intrinsic root calculation
constructs the actual parabolic image, its Goldschmidt--O'Nan input, fixed
space and displacement span. The earlier common-residual containment and
Sylow transport construct the mover. The possible centerless diagram case
is excluded when T_C ≤ X. These deductions feed the completed source
O'Nan contradiction with precisely the two actual residual image bounds.

This is a conditional assembly. The family calculations must still construct
`RootCalculation` through actual model equivalences, including the genuine
commutator lift in the nontrivial G₂(4) cover. No source-numbered long-root
exclusion is claimed here. The degree-one endpoint uses the earlier
two-central exclusion separately; this file never applies a cyclic actor
argument with 2^n - 1 = 1.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed pp.1201--1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
open Subgroup
open scoped IsMulCommutative
open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Representation.GoldschmidtONan
variable {G : Type*} [Group G]

/-- Elementary abelianness follows from the two commuting elementary factors. -/
theorem RootCalculation.elementary {T : Sylow 2 G} {L X : Subgroup G} {n : ℕ}
    (d : RootCalculation T L X n) : IsElementaryAbelian 2 (space T X) := by
  let := d.root_elementary
  let := d.commuting_elementary
  exact space_elementary ((residualRoot_le L X).trans inf_le_left) d.space_eq

/-- Each allowed residual description makes the actual parabolic normalize
X, and its root-group product makes it normalize V. -/
theorem RootCalculation.parabolic_le_actingGroup {T : Sylow 2 G}
    {L X : Subgroup G} {n : ℕ} (d : RootCalculation T L X n) :
    relativeNormalizer L (residualRoot L X) ≤ actingGroup (space T X) X :=
  relativeNormalizer_le_actingGroup d.space_eq
    (relativeNormalizer_normalizes_residual d.residual_description)

/-- All eight clauses of the O'Nan input are deductions from the model action
and the genuine ambient tight-embedding setup. -/
theorem RootCalculation.onanInput [Finite G] {T : Sylow 2 G} {z : G}
    {L X : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 (space T X)]
    (d : RootCalculation T L X n)
    (h : StandardSetup T z L) (hXL : X ≤ L) :
    GoldschmidtONan.Input (representation (space T X) X)
      (inducedActor (space T X) X (relativeNormalizer L (residualRoot L X))) := by
  apply onanInput_of_root_action h d.degree hXL d.parabolic_le_actingGroup
    d.image_cyclic d.image_card d.fixed_group
  simpa only [d.commutator_eq] using d.root_transitive

/-- The two linear spaces required by the existing source consumer are
identified using the literal parabolic action and its group commutator. -/
theorem RootCalculation.fixed_and_moved {T : Sylow 2 G}
    {L X : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 (space T X)]
    (d : RootCalculation T L X n) :
    let S := inducedActor (space T X) X (relativeNormalizer L (residualRoot L X))
    fixedSpace (representation (space T X) X) S =
        linearSpace (space T X) (commutingSylow T L) ∧
      displacementSpan (representation (space T X) X) S ⊤ =
        linearSpace (space T X) (residualRoot L X) := by
  constructor
  · rw [fixedSpace_inducedActor d.parabolic_le_actingGroup, d.fixed_group]
  · rw [displacementSpan_eq_commutator d.parabolic_le_actingGroup, d.commutator_eq]

private theorem contradiction_of_calculation [Finite G]
    {T : Sylow 2 G} {z g u : G} {L R X : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 (space T X)]
    (h : IntersectionSetup T z L g R) (d : RootCalculation T L X n)
    (hXL : X ≤ L) (hu : u ∈ R) (hu2 : orderOf u = 2)
    (hXL' : X ≤ L.conjBy g)
    (hRC : R ≤ centralizer (commutingSylow T L : Set G))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hgX : g ∈ normalizer (X : Set G))
    (himages : space T X ≤ X → SourceImageBounds (space T X) X) : False := by
  have hZV : residualRoot L X ≤ space T X := by rw [d.space_eq]; exact le_sup_left
  have hg := source_mover (T := T) (L := L) (R := R) (X := X)
    (Z := residualRoot L X) (u := u) h hu hu2 d.root_le_residual hXL' hRC
    d.space_eq htransport hgX
  have hinput := RootCalculation.onanInput (T := T) (z := z) (L := L) (X := X)
    (n := n) d h.toStandardSetup hXL
  have hspaces := RootCalculation.fixed_and_moved (T := T) (L := L) (X := X) (n := n) d
  have hcoverT : commutingSylow T L ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G) :=
    cover_reduction (T := T) (z := z) (L := L) (X := X)
      h.toStandardSetup hXL d.diagram_exception
  apply no_onan_action_of_source_image_bounds (T := T) (L := L) (X := X) (g := g)
    (Z := residualRoot L X)
    (inducedActor (space T X) X (relativeNormalizer L (residualRoot L X)))
  · exact hinput
  · exact hspaces.1
  · exact hspaces.2
  · exact hXL
  · exact d.root_nontrivial
  · exact hZV
  · exact d.root_le_residual
  · exact h.sylow_normalizes
  · exact d.normalizer_index
  · exact hg.1
  · exact hg.2
  · exact hcoverT
  · exact himages

/-- Consumer application with the actual modified residual. Remaining inputs
are the intrinsic root calculation, the indicated earlier common-residual
and Sylow-transport outputs, and the two genuine covered-action image bounds.
No O'Nan alternatives, Input, mover or Frattini equality are assumed. -/
theorem no_rootCalculation_of_source_image_bounds [Finite G]
    {T : Sylow 2 G} {z g u : G} {L R : Subgroup G} {n : ℕ}
    (h : IntersectionSetup T z L g R)
    (d : RootCalculation T L (modifiedCentralizerResidual L u) n)
    (hu : u ∈ R) (hu2 : orderOf u = 2)
    (hXL' : modifiedCentralizerResidual L u ≤ L.conjBy g)
    (hRC : R ≤ centralizer (commutingSylow T L : Set G))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hgX : g ∈ normalizer (modifiedCentralizerResidual L u : Set G))
    (himages : space T (modifiedCentralizerResidual L u) ≤ modifiedCentralizerResidual L u →
      SourceImageBounds (space T (modifiedCentralizerResidual L u))
        (modifiedCentralizerResidual L u)) : False := by
  let : IsElementaryAbelian 2 (space T (modifiedCentralizerResidual L u)) := d.elementary
  have hXL : modifiedCentralizerResidual L u ≤ L := (modifiedCentralizerResidual_le L u).trans
    ((involutionTwoResidual_le L u).trans inf_le_left)
  exact contradiction_of_calculation (T := T) (z := z) (g := g) (u := u) (L := L) (R := R)
    (X := modifiedCentralizerResidual L u) (n := n)
    h d hXL hu hu2 hXL' hRC htransport hgX himages

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
