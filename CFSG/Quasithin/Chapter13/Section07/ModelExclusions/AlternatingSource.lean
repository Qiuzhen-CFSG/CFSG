module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.FiveExclusion
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixChief
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SevenSource
/-!
# Original alternating natural alternatives for a contained component

The point-stabilizer rank bounds give n≤7, and the actual Sylow-fixed
point excludes n=5. The complete six- and seven-letter source branches
then give the original quotient alternative, product and commutator
identities, with the six-letter chief count on U_H itself. Their companion
source theorems retain the exact simultaneous printed point/plane markings.

Source: Aschbacher–Smith, 13.7.6(3), printed pp.938–940, L₁≤K branch.
The noncontained-component argument remains a separate source reduction.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- The only alternating natural degrees in the original contained branch are six and seven. -/
theorem alternating_degree_six_or_seven_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hrank : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    {n : ℕ} (hn : 5 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin n)) eK) :
    n = 6 ∨ n = 7 := by
  have hle := alternating_degree_le_seven_of_one_le d hH hKH hL₁K ρ hρ hrank eK hs
  have hne : n ≠ 5 := by
    intro he
    subst n
    exact not_five_natural_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  omega

/-- Every algebraic clause of original 13.7.6(3) in the contained branch,
matching the exact earlier-source consumer including its unquotiented chief count. -/
theorem alternating_source_of_one_le
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hrank : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    {n : ℕ} (hn : 5 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin n)) eK) :
    Section08.Source.UH H V₃ = ⁅Section08.Source.UH H V₃,K⁆ ∧
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    ((n = 6 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Section08.CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneRepresentation H V₃ (sourceOne L T V₁) (le_sup_left.trans hH.1.2))) ∨
      (n = 7 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))) := by
  rcases alternating_degree_six_or_seven_of_one_le d hH hF9 hKH hK hL₁K ρ hρ hrank hn eK hs with rfl | rfl
  · obtain ⟨hg,hp,hq,hc⟩ := six_source_case_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
    exact ⟨hg,hp,Or.inl ⟨rfl,hq,hc⟩⟩
  · obtain ⟨hg,hp,hq,_⟩ := seven_source_case_of_one_le d h hH hF9 hcentral hKH hK hL₁K ρ hρ hrank eK hs
    exact ⟨hg,hp,Or.inr ⟨rfl,hq⟩⟩
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
