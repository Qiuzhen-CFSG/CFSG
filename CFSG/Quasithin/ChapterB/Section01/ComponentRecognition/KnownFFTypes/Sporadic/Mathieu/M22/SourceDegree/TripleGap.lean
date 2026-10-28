module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.Preparation

/-!
# The genuine source action in the triple-cover degree window

Cover recognition constructs an actual isomorphism from the source component
to the matrix triple cover. Pulling back the same action along its inverse
preserves faithfulness and irreducibility. The unconditional source bound
then places this action in the binary window 12, 18, 24, or central-field
window 6, 9, 12.

The proved arbitrary-module gap excludes the two larger degrees and gives
binary degree twelve for this same component action. No ambient recognition,
absolute irreducibility, prescribed Schur field, or additional representation
exclusion is an input to the unconditional source endpoint.

Source: Guralnick–Malle I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7;
Aschbacher–Smith, printed pp.393–394, 451–452 and 457.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

universe u

variable {G : Type*} {V : Type u} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The source action has an actual cover marking and the same faithful,
 irreducible action in the proved degree window. -/
theorem exists_source_triple_degree_action (h : SourceHypotheses ρ L)
    (hc : Nat.card (center L) = 3) :
    ∃ e : L ≃* M22TripleCover,
      let σ : Representation (ZMod 2) M22TripleCover V :=
        (ρ.comp L.subtype).comp e.symm.toMonoidHom
      Function.Injective σ ∧ σ.IsIrreducible ∧ Module.finrank (ZMod 2) V ≤ 24 := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hc h.quotient
  refine ⟨e, (h.faithful.comp L.subtype_injective).comp e.symm.injective, ?_,
    source_triple_finrank_le_twenty_four ρ L h hc⟩
  exact (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
    e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance

/-- The source endpoint conditional on the two explicit central-field degree
 exclusions. Final assembly must discharge both premises. -/
theorem source_triple_finrank_le_twelve_of_field_exclusions
    (h : SourceHypotheses ρ L) (hc : Nat.card (center L) = 3)
    (h9 : M22TripleCover.DegreeTwentyFour.CentralFieldDegreeExclusion.{u} 9)
    (h12 : M22TripleCover.DegreeTwentyFour.CentralFieldDegreeExclusion.{u} 12) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  obtain ⟨e, hf, hi, hd⟩ := exists_source_triple_degree_action ρ L h hc
  let σ : Representation (ZMod 2) M22TripleCover V :=
        (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : σ.IsIrreducible := hi
  exact (M22TripleCover.DegreeTwentyFour.finrank_eq_twelve_of_field_exclusions
    σ hf h9 h12 hd).le

/-- The source triple-cover component acts on a binary space of degree twelve.
The actual cover marking transports the original action into the proved gap. -/
theorem source_triple_finrank_eq_twelve (h : SourceHypotheses ρ L)
    (hc : Nat.card (center L) = 3) : Module.finrank (ZMod 2) V = 12 := by
  obtain ⟨e, hf, hi, hd⟩ := exists_source_triple_degree_action ρ L h hc
  let σ : Representation (ZMod 2) M22TripleCover V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : σ.IsIrreducible := hi
  exact M22TripleCover.DegreeTwentyFour.finrank_eq_twelve_of_le_twenty_four σ hf hd

/-- The degree bound needed by source recognition, with every triple-cover
representation exclusion discharged. -/
theorem source_triple_finrank_le_twelve (h : SourceHypotheses ρ L)
    (hc : Nat.card (center L) = 3) : Module.finrank (ZMod 2) V ≤ 12 :=
  (source_triple_finrank_eq_twelve ρ L h hc).le

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
