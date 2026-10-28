module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.Preparation
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.SimpleDisplacement
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.SimpleGap
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.TripleGap

/-!
# The source degree bound for the M₂₂ branch

The binary-cover theorem gives actual simple or triple-cover markings. For the
simple cover, the source cubic ratio and the inner and ambient involution
displacement bounds give degree at most thirty; the arbitrary-module gap then
gives degree ten. For the triple cover, the cubic ratio, the scalar action of
outer elements, and the extraspecial displacement bound give degree at most
twenty-four; the arbitrary-module gap gives degree twelve.

Thus every source action has binary degree at most twelve, with no additional
degree, recognition, field-of-definition, or full-normalizer hypothesis. This
discharges the numerical premise of
`SourceRecognition.source_componentModels_of_degree_le_twelve`; identification
of the component modules and permissible ambient actions belongs to that
source-recognition assembly.

Source: Aschbacher–Smith, Chapter K, printed pp.451–452 and 457;
Guralnick–Malle I, Proposition 5.1 and Theorem 6.6/Table 6.7.
-/

public section
open Subgroup Theory.GroupTheory Representation
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The actual source action reduces to a simple cover or a triple cover in the
specified degree window. These are genuine group isomorphisms. -/
theorem source_cover_degree_cases (h : SourceHypotheses ρ L) :
    Nonempty (L ≃* M22) ∨
      (Nonempty (L ≃* M22TripleCover) ∧
        (Module.finrank (ZMod 2) V = 12 ∨ Module.finrank (ZMod 2) V = 18 ∨
          Module.finrank (ZMod 2) V = 24)) := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := h.quotient
  rcases M22BinaryCovers.center_card_eq_one_or_three_of_binary_irreducible
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e with hc | hc
  · exact Or.inl ⟨M22BinaryCovers.simpleEquiv e hc⟩
  · exact Or.inr ⟨M22TripleCover.nonempty_mulEquiv hc h.quotient,
      source_triple_finrank_cases ρ L h hc⟩

/-- Every faithful binary source action with central quotient M₂₂ and cubic
ratio at most two has degree at most twelve. Both cover branches and their
arbitrary-module degree exclusions are discharged. -/
theorem source_finrank_le_twelve (h : SourceHypotheses ρ L) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := h.quotient
  rcases M22BinaryCovers.center_card_eq_one_or_three_of_binary_irreducible
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e with hc | hc
  · let eL := M22BinaryCovers.simpleEquiv e hc
    exact source_simple_finrank_le_twelve_of_le_thirty ρ L h eL
      (source_simple_finrank_le_thirty ρ L h eL)
  · exact source_triple_finrank_le_twelve ρ L h hc

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
