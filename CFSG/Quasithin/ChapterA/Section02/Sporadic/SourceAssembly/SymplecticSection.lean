module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore

/-!
# A symplectic alternative for the Fischer source section

An actual embedding PSp₆(2) into the fixed U₆(2) carrier lets the original
proper-section induction use the already proved nonabelian simple symplectic
group and its three-rank. Pull back its image along the literal Fischer
quotient maps; no splitting or quasithinness of a central quotient is used.

The final application handles all sporadic Case II branches without the
prime-core identity. It retains the concrete symplectic embedding, Fischer
quotient maps, McL model comparison and O'Nan compatible lift as independent
model inputs. Constructing these inputs is separate from this source adapter.

Source: Aschbacher–Smith A.2.19, printed pp.40–41, via the symplectic section
of the unitary entry in GLS3 Table 5.3t.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [IsQuasisimple G]

public theorem false_of_cover_unitary_data_of_symplectic_embedding
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* H)
    (d : InvolutionCentralizerQuotientData H Theory.SpecificGroups.U6Two.Carrier)
    (j : ClassicalGroup.PSp 3 (ZMod 2) →* Theory.SpecificGroups.U6Two.Carrier)
    (hj : Function.Injective j) : False := by
  let : IsSimpleGroup (ClassicalGroup.PSp 3 (ZMod 2)) := leechPSp6Two_simple
  let d' := (d.restrictTarget j.range).mapTarget (MonoidHom.ofInjective hj).symm
  exact false_of_cover_centralizer_quotient ih hG hK e d'
    leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

public theorem sporadic_caseII_of_symplectic_embedding
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G))
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (j : ClassicalGroup.PSp 3 (ZMod 2) →* Theory.SpecificGroups.U6Two.Carrier)
    (hj : Function.Injective j)
    (d23 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G, (projection e).comp F = ONan.Cover.projection) :
    False := by
  rcases WithoutPrimeCore.sporadic_cover_reduction h ih hspor with hm | hr
  · obtain ⟨e⟩ := hm
    exact WithoutPrimeCore.cover_mcl_of_comparison h ih e comparison
  · rcases hr with ho | hr
    · obtain ⟨e⟩ := ho
      obtain ⟨F,hF⟩ := hlift e
      exact WithoutPrimeCore.cover_onan_of_compatible_lift h ih e F hF
    · rcases hr with h22 | hr
      · obtain ⟨e⟩ := h22
        exact false_of_cover_unitary_data_of_symplectic_embedding ih h.1 h.2.1 e
          fi22_unitary_data j hj
      · rcases hr with h23 | h24
        · obtain ⟨e⟩ := h23
          exact false_of_cover_unitary_data_of_symplectic_embedding ih h.1 h.2.1 e
            (fischer_unitary_data d23) j hj
        · obtain ⟨e⟩ := h24
          exact false_of_cover_unitary_data_of_symplectic_embedding ih h.1 h.2.1 e
            (fischer_unitary_data d24) j hj

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
