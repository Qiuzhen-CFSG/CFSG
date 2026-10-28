module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrattiniMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphDescent

/-!
# Feeding the marked section into Frattini graph descent

The exact binary section supplies the full component Frattini marking used by
the graph extension.  This adapter keeps the graph projection, crossing and
field data explicit while discharging the marking and equivariance premises
from the literal section.
-/

open Subgroup Matrix Representation
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
attribute [local instance] SecondaryActionData.normal
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}
set_option backward.isDefEq.respectTransparency false

/-- A literal degree-sixteen binary section supplies the graph-descent data on
the same component and quotient. -/
def source_frattini_graph_data_of_section
    (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
        (mark (QuotientGroup.mk' (pCore 2 s.component) z)))
    (correction : GL (Fin 3) Matrix.PSL3Four.F)
    (field : Matrix.PSL3Four.F ≃+* Matrix.PSL3Four.F)
    (hgraph : (MulAut.congr mark)
      (s.action ⟨c.t,root_normalized c D c.crossing_mem⟩) =
        linearConj Matrix.PSL3Four.F correction *
          graph Matrix.PSL3Four.F * fieldAction Matrix.PSL3Four.F field) :
    FrattiniGraphData (F := Matrix.PSL3Four.F) s.component
      (cubicExtension s X) le_sup_left := by
  let hm := marking_of_section s D h mark X hXr W ρ b hd hnt
  let e := Classical.choose hm
  have he := Classical.choose_spec hm
  exact sourceFrattiniGraphData s D h (by
    simpa using Matrix.PSL3Four.card_F) mark X φ hφ hsquare e he
    correction field hgraph

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
