module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CatalogueWitnesses

/-!
# The complete local catalogue in the original Chapter 9 field-two consumer

The original full rank-one catalogue now constructs all three concrete binary
models required by the Chapter 9 argument. Both dihedral exclusions occur on
the literal source actions before the corresponding recognition step. Applying
the checked distance and field argument then gives distance three and both
adjacent field orders two.

Only the earlier Chapter 8 exchange output remains as a source premise here;
the ChapterEightSource assembly supplies it from the original geometry.
Source: DGS, Groups and Graphs (1985), 8.6, 9.3--9.4 and 9.10, pp.139--150.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The original field-two conclusion uses the full source catalogue, without
three separately supplied concrete binary-model witnesses. -/
theorem reduced_critical_fields_two_from_full_catalogue
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))

 :
    let Γ := Reduction.reducedFamily L S₀
    b Γ = 3 ∧
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card F = 2 ∧ Nat.card K = 2 ∧
          Nonempty ((graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) ∧
          Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,K)) := by
  obtain ⟨Mα, Mβ, Mα'⟩ :=
    reduced_critical_binary_models_of_source h models hc hab hd hb hcomm htriv h8
  exact reduced_critical_fields_two_of_catalogue h models hc hab hd hb hcomm htriv h8 Mα Mβ Mα'

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
