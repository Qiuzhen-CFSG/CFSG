module
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.SymplecticSection
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary.SymplecticEmbedding
/-!
# The actual symplectic section closes the Fischer classical input

The concrete PSp₆(2) embedding in the fixed U₆(2) model discharges the
classical section hypothesis in all Fischer cover consumers. In the simple
case the same proper-section induction argument applies, so the Fi₂₃ and
Fi₂₄′ source maps need no extra restriction on their kernels.

The full sporadic source applications retain only the independently owned
Fi₂₃/Fi₂₄′ centralizer maps, McL comparison and original-context O’Nan lift.
The Fi₂₂ cover branch itself has no further model input.
Source: Aschbacher–Smith A.2.19, printed pp.40–41.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v
variable {G : Type u} [Group G] [Finite G]

theorem cover_fi22 [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi22.Carrier) : False := by
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.U6Two.SymplecticEmbedding.exists_embedding
  exact false_of_cover_unitary_data_of_symplectic_embedding ih hG hK e fi22_unitary_data j hj

theorem cover_fischer_of_source_data [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    {H : Type v} [Group H] (e : G ⧸ center G ≃* H)
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier) : False := by
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.U6Two.SymplecticEmbedding.exists_embedding
  exact false_of_cover_unitary_data_of_symplectic_embedding ih hG hK e (fischer_unitary_data d) j hj

theorem simple_fischer_of_source_data [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    {H : Type v} [Group H] (e : G ≃* H)
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier) : False := by
  let : IsQuasisimple G := simple_quasisimple hna
  let q : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hna)).trans QuotientGroup.quotientBot
  exact cover_fischer_of_source_data ih hG hK (q.trans e) d

theorem sporadic_caseI_of_fischer_sections [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (hspor : KnownSimple.IsSporadicCarrier G)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  rcases sporadic_simple_reduction ih hG hK hna hspor with hm | hr
  · exact ⟨.sporadic hm, fun hs => theoremC_of_theoremBSporadicModel hs hm⟩
  · rcases hr with h23 | h24
    · obtain ⟨e⟩ := h23
      exact (simple_fischer_of_source_data ih hG hK hna e d23).elim
    · obtain ⟨e⟩ := h24
      exact (simple_fischer_of_source_data ih hG hK hna e d24).elim

theorem sporadic_caseII_of_remaining_model_inputs [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G))
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G, (projection e).comp F = ONan.Cover.projection) :
    False := by
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.U6Two.SymplecticEmbedding.exists_embedding
  exact sporadic_caseII_of_symplectic_embedding h ih hspor comparison j hj d23 d24 hlift

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
