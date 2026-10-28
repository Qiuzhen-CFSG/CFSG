module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers

/-!
# Applying the completed involution geometry to the J₂ source graph

The source order and selected geometry of 47.1 discharge the two remaining
premises of the prime-local and suborbit calculations. The same seed, ambient
subgroups, and chosen order-three subgroup are retained. In particular the
four suborbits and the A₅ edge fixer now follow from the source seed alone.
The graph-uniqueness assembly still owns the remaining frame and triangle
arguments; this module supplies its earlier involution-geometry inputs.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.5, pp.259–263.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Applications

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual prime-local consumer, with both the order and selected geometry
constructed from the seed. The root representative retains its marked models. -/
theorem source_prime_local (D : Seed G) :
    ∃ S : SelectedGeometry D,
      PrimeNormalizers.FiveLocal.SourceConclusion D S.t ∧
      PrimeNormalizers.ThreeLocal.SourceConclusion D := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  exact ⟨S, PrimeNormalizers.source_prime_local_of_selectedGeometry (card_eq D) S⟩

/-- The four-suborbit input to the source graph assembly, without any additional
order, centralizer, normalizer, or representative premise. -/
theorem fourSuborbits (D : Seed G) : FourSuborbits D := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  exact PrimeNormalizers.fourSuborbits_of_selectedGeometry (card_eq D) S

/-- The literal pointwise fixer of every edge at the base is A₅. -/
theorem edgeFixer_equiv (D : Seed G) {Y : D.Vertex}
    (hY : D.graph.Adj D.base Y) :
    Nonempty (edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  exact PrimeNormalizers.edgeFixer_equiv_of_selectedGeometry (card_eq D) S hY

/-- The exact earlier-source premises used by the 47.10 frame consumer,
including the literal centralizer C_G(B), endpoint inclusions, and relative
proper-overgroup condition in N_G(X). Only the frame itself remains an input. -/
theorem edgeFrame_calculations (D : Seed G) (F : EdgeFrame D) :
    Nonempty (F.K ≃* alternatingGroup (Fin 5)) ∧
    D.X ⊔ F.y.val ≤ F.K ∧
    (∀ U : Subgroup G, edgeFixer G D.base F.y ≤ U →
      U ≤ normalizer (D.X : Set G) → U ≠ normalizer (D.X : Set G) →
      U ≤ centralizer (D.X : Set G)) := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  exact PrimeNormalizers.edgeFrame_calculations_of_selectedGeometry (card_eq D) S F

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Applications
