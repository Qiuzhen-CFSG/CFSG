module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphActor
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphDescent

/-!
# Application of the original crossing to Frattini descent

The source frame supplies the crossing equation required by the literal
Frattini graph construction. The full component marking and cubic projection
square remain the original ones. The generation premise is the whole-radical
source premise used to construct that frame.
Source: Aschbacher–Smith B.4.14 and original 4.3.16, printed pp.98,618–619.
-/

public noncomputable section
open Subgroup Matrix Representation
open scoped MatrixGroups
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
attribute [local instance] ZMod.algebra SecondaryActionData.normal
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The original generation premise discharges the crossing equation in
Frattini descent, for the same full marking and cubic projection square. -/
theorem source_full_frattini_ordinary_of_generation (s : SecondaryActionData c 2)
    {d : MSData c 2} (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hg : EndgameSieve.SecondaryActionData.ActionGeneration s)
    (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F)
    (hφ : Function.Surjective φ)
    (hsquare : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      ProjectiveSpecialLinearGroup.toPGL (mark (QuotientGroup.mk' (pCore 2 s.component) b)))
    (e : Frattini s.component ≃* Multiplicative (TraceZero F))
    (he : ∀ (b : s.component) v,
      (e (coreAction s.component (b : rootNormalizer c) v)).toAdd =
        projectiveSpecialAdjoint F (mark (QuotientGroup.mk' (pCore 2 s.component) b))
          (e v).toAdd)
    (g : cubicExtension s X) (v : Frattini s.component) :
    (e (coreAction s.component (g : rootNormalizer c) v)).toAdd =
      projectiveAdjoint F (φ g) (e v).toAdd := by
  obtain ⟨correction,field,hgraph⟩ :=
    EndgameSieve.SecondaryActionData.source_crossing_graph_form s m D hg hF mark
  exact source_full_frattini_ordinary s D h hF mark X φ hφ hsquare e he
    correction field hgraph g v

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
