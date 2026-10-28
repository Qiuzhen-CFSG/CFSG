module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreFrattiniFixed
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreExactSection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrattiniMarkingApplication
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphActorApplications
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCubicFrame
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniRootPlane

/-!
# The source-action Frattini contradiction

This is the weak `SecondaryActionData` adapter for the marked Frattini
argument.  It uses the literal component and cubic extension throughout, so
the upper bound is the source component bound and the lower bound is on the
same quotient and the same cubic action.  Root-plane preservation and
outerness provide the split diagonal normal form through the root-plane
theorem; both remain explicit premises of this adapter.

The exact binary section, the source graph crossing, and the cubic extension
can therefore be assembled in one final consumer without introducing the
legacy strict core-enlargement record.
Source: Aschbacher--Smith, original 4.3.14--16 and the conclusion of 4.3.2,
printed pp.617--619; B.4.14, printed p.98.
-/

public noncomputable section
open Matrix Subgroup Representation
open scoped MatrixGroups
open Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
attribute [local instance] ZMod.algebra SecondaryActionData.normal
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

abbrev SourceActionFrattiniGraphData {F : Type*} [Field F]
    (s : SecondaryActionData c 2) (X : Subgroup G) :=
  FrattiniGraphData (F := F) s.component (cubicExtension s X) le_sup_left

/-! The literal inclusion of the source cubic into its extension. -/
abbrev sourceActionCubicInclusion (s : SecondaryActionData c 2) (X : Subgroup G)
    (hXr : X ≤ rootNormalizer c) : X →* cubicExtension s X :=
  cubicSourceInclusion s X hXr

theorem source_action_frattini_fixed_card_ge
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX : Nat.card X = 3)
    (hXr : X ≤ rootNormalizer c)
    (dF : SourceActionFrattiniGraphData (F := F) s X)
    (hF : Nat.card F = 4) (x : X) (hx : x ≠ 1) (b : Bool)
    (hout : (pglEquivInnerDiagonal F
      (dF.projection (sourceActionCubicInclusion s X hXr x))).val ∉
        MulAut.innerSubgroup PSL(3,F))
    (hroot : (rootPlane F b).map
      (pglEquivInnerDiagonal F
        (dF.projection (sourceActionCubicInclusion s X hXr x))).val.toMonoidHom =
      rootPlane F b) :
    letI : MulDistribMulAction X (Frattini s.component) :=
      MulDistribMulAction.compHom _ ((coreAction s.component).comp
        ((cubicExtension s X).subtype.comp (sourceActionCubicInclusion s X hXr)))
    256 ≤ Nat.card (FixedPoints.subgroup X (Frattini s.component)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hx3 : x ^ 3 = (1 : X) := by
    simpa only [hX] using (pow_card_eq_one' (x := x))
  exact dF.fixed_card_ge_of_rootPlane hF (sourceActionCubicInclusion s X hXr) x
    (zpowers_eq_top_of_prime_card hX hx) hx3 b hout hroot

/-- The literal upper and lower bounds contradict each other for an outer
source cubic preserving a root plane. -/
theorem source_action_marked_frattini_false_of_rootPlane
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {d : MSData c 2} (m : Nonblock.RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2)
    (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hXK : X ≤ (K c).coreCenterIn 2) (hXr : X ≤ rootNormalizer c)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (dF : SourceActionFrattiniGraphData (F := F) s X)
    (hF : Nat.card F = 4) (x : X) (hx : x ≠ 1) (b : Bool)
    (hout : (pglEquivInnerDiagonal F
      (dF.projection (sourceActionCubicInclusion s X hXr x))).val ∉
        MulAut.innerSubgroup PSL(3,F))
    (hroot : (rootPlane F b).map
      (pglEquivInnerDiagonal F
        (dF.projection (sourceActionCubicInclusion s X hXr x))).val.toMonoidHom =
      rootPlane F b) : False := by
  let actionUpper : MulDistribMulAction X (Frattini s.component) :=
    MulDistribMulAction.compHom _ ((coreAction s.component).comp (inclusion hXr))
  let actionLower : MulDistribMulAction X (Frattini s.component) :=
    MulDistribMulAction.compHom _ ((coreAction s.component).comp
      ((cubicExtension s X).subtype.comp (sourceActionCubicInclusion s X hXr)))
  have hcomp :
      (cubicExtension s X).subtype.comp (sourceActionCubicInclusion s X hXr) =
        inclusion hXr := by
    ext y
    rfl
  have hact : actionLower = actionUpper := by
    apply MulDistribMulAction.ext
    funext a v
    change (coreAction s.component)
        (((cubicExtension s X).subtype.comp
          (sourceActionCubicInclusion s X hXr)) a) v =
      (coreAction s.component) (inclusion hXr a) v
    rw [hcomp]
  let U : Subgroup (Frattini s.component) := by
    letI := actionUpper
    exact FixedPoints.subgroup X (Frattini s.component)
  let L : Subgroup (Frattini s.component) := by
    letI := actionLower
    exact FixedPoints.subgroup X (Frattini s.component)
  have hu : Nat.card U ≤ 16 := by
    letI := actionUpper
    have hu0 := component_frattini_fixed_card_le m D s X hX3 hXK hXr hfix
    dsimp at hu0
    change Nat.card (FixedPoints.subgroup X (Frattini s.component)) ≤ 16
    exact hu0
  have hl : 256 ≤ Nat.card L := by
    letI := actionLower
    have hl0 := source_action_frattini_fixed_card_ge s X hX3 hXr dF hF x hx b hout hroot
    change 256 ≤ Nat.card (FixedPoints.subgroup X (Frattini s.component))
    exact hl0
  have hUL : U = L := by
    dsimp [U, L]
  have hl' : 256 ≤ Nat.card U := by simpa [hUL] using hl
  omega

/-! Assemble the graph data from the exact section and the source crossing. -/
def source_action_frattini_graph_data_of_section_generation
    (s : SecondaryActionData c 2) {d : MSData c 2}
    (m : Nonblock.RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hg : EndgameSieve.SecondaryActionData.ActionGeneration s)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
    (X : Subgroup G) (hXr : X ≤ rootNormalizer c)
    (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (s.component.map (rootNormalizer c).subtype ⊔ X : Subgroup G) W)
    (b : BinaryConjugationSection
      (s.component.map (rootNormalizer c).subtype ⊔ X)
      ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)
      ((frattini ((s.component.map (rootNormalizer c).subtype).pCoreIn 2)).map
        ((s.component.map (rootNormalizer c).subtype).pCoreIn 2).subtype) ρ)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) W = 16)
    (hnt : ¬ (s.component.map (rootNormalizer c).subtype).subgroupOf
      (s.component.map (rootNormalizer c).subtype ⊔ X) ≤ ρ.ker)
    (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) Matrix.PSL3Four.F)
    (hφ : Function.Surjective φ)
    (hsquare : ∀ z : s.component, φ (cubicComponentInclusion s X z) =
      ProjectiveSpecialLinearGroup.toPGL
        (mark (QuotientGroup.mk' (pCore 2 s.component) z))) :
    SourceActionFrattiniGraphData (F := Matrix.PSL3Four.F) s X := by
  let hexists := EndgameSieve.SecondaryActionData.source_crossing_graph_form s m D hg
    (by simpa using Matrix.PSL3Four.card_F) mark
  let correction := Classical.choose hexists
  let field := Classical.choose (Classical.choose_spec hexists)
  have hgraph := Classical.choose_spec (Classical.choose_spec hexists)
  exact source_frattini_graph_data_of_section s D h mark X hXr W ρ b hd hnt φ hφ
    hsquare correction field hgraph

/-! The final source consumer discharges section marking and graph data. -/
theorem source_action_marked_frattini_false_of_generation
    {d : MSData c 2} (m : Nonblock.RootCoordinates d)
    (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hg : EndgameSieve.SecondaryActionData.ActionGeneration s)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
    (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hXK : X ≤ (K c).coreCenterIn 2) (hXr : X ≤ rootNormalizer c)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hcomm : ⁅secondary c, X⁆ ≤ (secondary c).pCoreIn 2)
    (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) Matrix.PSL3Four.F)
    (hφ : Function.Surjective φ)
    (hsquare : ∀ z : s.component, φ (cubicComponentInclusion s X z) =
      ProjectiveSpecialLinearGroup.toPGL
        (mark (QuotientGroup.mk' (pCore 2 s.component) z)))
    (x : X) (hx : x ≠ 1) (b : Bool)
    (hout : (pglEquivInnerDiagonal Matrix.PSL3Four.F
      (φ (sourceActionCubicInclusion s X hXr x))).val ∉
        MulAut.innerSubgroup PSL(3,Matrix.PSL3Four.F))
    (hroot : (rootPlane Matrix.PSL3Four.F b).map
      (pglEquivInnerDiagonal Matrix.PSL3Four.F
        (φ (sourceActionCubicInclusion s X hXr x))).val.toMonoidHom =
      rootPlane Matrix.PSL3Four.F b) : False := by
  obtain ⟨W, iAdd, iMod, ρ, sec, hi, hd, hnt⟩ :=
    exact_section m s D h X hX3 hXK hXr hfix hcomm mark
  letI : AddCommGroup W := iAdd
  letI : Module (ZMod 2) W := iMod
  letI : ρ.IsIrreducible := hi
  let dF := source_action_frattini_graph_data_of_section_generation s m D h hg mark X hXr
    W ρ sec hd hnt φ hφ hsquare
  have hproj : dF.projection (sourceActionCubicInclusion s X hXr x) =
      φ (sourceActionCubicInclusion s X hXr x) := by
    rfl
  rw [← hproj] at hout hroot
  apply source_action_marked_frattini_false_of_rootPlane m D s X hX3 hXK hXr hfix dF
    (by simpa using Matrix.PSL3Four.card_F) x hx b hout hroot

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
