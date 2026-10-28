module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ContainedLinearModels
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearFourSource
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.AlternatingSource
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.SourcePlaneBounds
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary

/-!
# The contained ordinary binary model sieve

The actual ordinary plane actor supplies the three-rank bound on C_G(V₂).
It excludes the binary degree-five and ten-dimensional rows. A contained
binary degree-four natural component would force the covered A₆ quotient,
whose center has order three, contradicting the original ordinary A₆ quotient.
The alternating natural rows reduce to degree six by the same source rank
bound and the covered seven-letter case.

All conclusions retain the literal K/O₂(K) and raw UH/V₁ markings.
Source: Aschbacher–Smith 13.7.6 and 13.7.18, printed pp.938–940,945.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section05.AmbientSource Section05.PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

theorem plane_centralizer_rank_of_noncentral
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥) :
    primeRank 3 (centralizer (V₂ : Set G)) ≤ 1 := by
  obtain ⟨hx,hk⟩ := Ordinary.planeActor_action_source d eL
  have hm' : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥ := d.first_normalizer.symm ▸ hm
  exact (source_plane_core_and_rank d (planeActor (L := L) (V₂ := V₂))
    (planeActor_le.trans inf_le_right) (planeActor_normalized d)
    planeActor_twoPerfect hx hk hm').2

variable [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
  (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
  (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
  (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hL₁K : sourceOne L T V₁ ≤ K)
  (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
    (Additive (Section08.Source.Utilde H V₃ V₁)))
  (hρ : IsConjugation H V₃ V₁ ρ)

include d eL h1221 hH h hm hK hL₁K hρ in
theorem linear_four_false
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 4) eK) : False := by
  let c := BinaryLinear.OuterCyclic.slEquivLinear 4
  have hs' : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 4) (eK.trans c) := by
    obtain ⟨hst,e,he⟩ := hs
    exact ⟨hst,e,he⟩
  obtain ⟨ec⟩ := (ModelExclusions.linear_four_source_case_of_one_le d h1221 hH h
    (source_parabolic_centralizer d eL h1221 hm) hKH hK hL₁K ρ hρ (eK.trans c) hs').2.1
  have hc := Nat.card_congr (centerCongr (ec.symm.trans eL)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega

include d eL hH hm hL₁K hρ in
theorem linear_five_false
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 5) eK) : False := by
  have hd := ModelExclusions.specialLinear_dimension_le_four_of_one_le d hH hKH hL₁K ρ hρ
    (plane_centralizer_rank_of_noncentral d eL hm) eK hs
  omega

include d eL h1221 hH h hm hK hL₁K hρ in
theorem alternating_natural_degree_six {n : ℕ} (hn : 5 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) eK) : n = 6 := by
  have hr := plane_centralizer_rank_of_noncentral d eL hm
  rcases ModelExclusions.alternating_degree_six_or_seven_of_one_le d hH h hKH hK hL₁K
    ρ hρ hr hn eK hs with h6 | h7
  · exact h6
  · subst n
    exact (ModelExclusions.not_seven_natural_of_ordinary_one_le d h1221 hH h
      (source_parabolic_centralizer d eL h1221 hm) hKH hK hL₁K ⟨eL⟩ ρ hρ hr eK hs).elim

include d eL hH hm hL₁K hρ in
theorem ten_dimensional_false
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) SL5TenDimensional.Group E) [Representation.IsIrreducible τ]
    (hdim : Module.finrank (ZMod 2) E = 10)
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) : False :=
  ModelExclusions.not_irreducible_ten_of_one_le d hH hKH hL₁K ρ hρ
    (plane_centralizer_rank_of_noncentral d eL hm) τ hdim eK hs

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource