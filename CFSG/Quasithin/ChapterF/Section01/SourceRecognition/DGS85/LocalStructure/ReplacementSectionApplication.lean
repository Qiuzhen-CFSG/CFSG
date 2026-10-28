module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementApplication

/-!
# The replacement simple section in the original reduced F1.11 graph

The reduced triple supplies every local hypothesis of the constructed
residual-moving section. The displayed inclusion identifies its whole
replacement span with the original parabolic-core closure in the original
completion. The selected section retains its own kernel, original actor,
actual closure Sylow, and fixed-space index bound.

This removes the section's Sylow-generation and residual-fixed premises;
it does not identify its faithful image with a catalogue model or assert
that the escaping actor survives on it. The central neighboring-center
branch and the nonlinear 6.5 contradiction remain separate obligations.

Source: DGS, Groups and Graphs (1985), reduction p.95 and6.4, pp.120--121;
Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual F1.11 section construction, with the original completion inclusion and full-endpoint closure retained. -/
theorem reduced_replacement_simple_quadratic_section (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (hnc : ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S))) :
    let P := fun j => (P₀ L S j).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    V.map (G₀ L S).subtype = conjugateSpanBy (sylowCenterSpan (P₀ L S i))
      (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))) ∧
    ∃ U C : Subgroup (G₀ L S), U ≤ V ∧ ∃ (W : Type u) (_ : AddCommGroup W)
      (_ : Module (ZMod 2) W) (_ : Finite W) (ρ : Representation (ZMod 2) X W),
      Nonempty (BinaryConjugationSection X U C ρ) ∧ IsIrreducible ρ ∧
      ρ.ker.map X.subtype = commutatorPreimage X U C ∧ pCore 2 X ≤ ρ.ker ∧
      Function.Injective (imageRepresentation ρ) ∧ pCore 2 (actionImage ρ) = ⊥ ∧
      fixedSpace (imageRepresentation ρ) (pResidual 2 (actionImage ρ)) = ⊥ ∧
      (∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = ((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2 ⊓ X ∧
        ∃ R : Sylow 2 (actionImage ρ), (R : Subgroup (actionImage ρ)) =
          (T : Subgroup X).map (actionHom ρ) ∧ GeneratedByFixedSpace (imageRepresentation ρ) R) ∧
      ∃ A : Subgroup (G₀ L S), A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
        IsQuadratic (imageRepresentation ρ) ((A.subgroupOf X).map (actionHom ρ)) ∧
        Nat.card (W ⧸ fixedSpace (imageRepresentation ρ)
          ((A.subgroupOf X).map (actionHom ρ))) ≤ ((P (other i)).pCoreIn 2).relIndex A := by
  constructor
  · exact reduced_replacement_span_image h i
  · exact source_replacement_simple_quadratic_section (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i
      ((inter_core_local_normal_iff (reduced_triple h) i _).mp hn) hnc

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
