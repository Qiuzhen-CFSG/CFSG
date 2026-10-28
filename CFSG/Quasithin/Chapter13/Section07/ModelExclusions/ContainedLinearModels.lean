module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneStabilizers
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointStabilizerRanks

/-!
# Original contained-component binary linear exclusions

When L₁≤K, an actual vector of V₂ survives in the literal component
section. Every model-point stabilizer of three-rank at least two then
contradicts the earlier source bound on C_G(V₂). This proves n≤4 for the
binary natural linear models and excludes both SL₅(2) exterior models,
as well as every ten-dimensional irreducible SL₅(2) model.

The only earlier rank premise is13.5.4(3), whose source producer is
Section05.AmbientSource.SourcePlaneBounds.source_plane_core_and_rank.
No marked-point nonzeroness, component normality, generation or point
stabilizer rank remains a premise. The branch L₁≰K and the subsequent
n=3 elimination are separate parts of the source proof.

Source: Aschbacher–Smith,13.7.6(1–2), printed pp.938–939.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open PointRanks
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
  (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
  (hKH : K ≤ H) (hL₁K : sourceOne L T V₁ ≤ K)
  (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
    (Additive (Section08.Source.Utilde H V₃ V₁)))
  (hρ : IsConjugation H V₃ V₁ ρ)
  (hcentral : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
include d hH hKH hL₁K hρ hcentral

private theorem section_rank_bound_impossible
    (hbound : ∀ u : commutatorImage H V₃ V₁ K,
      (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0 →
        SectionPointRankBound H V₃ V₁ K ρ hKH u) : False := by
  obtain ⟨v, hv⟩ := exists_plane_section_nonzero d hKH hL₁K ρ hρ
  let hu := plane_vector_mem_commutator d hKH hL₁K ρ hρ v
  obtain ⟨hs, P, hrank, hP⟩ := hbound ⟨_, hu⟩ hv
  have hHN : H ≤ normalizer (V₁ : Set G) := d.first_normalizer ▸ hH.2.1
  have hr := section_point_rank_le_plane_centralizer d hHN hKH ρ hρ v hu hv hs P
    (fun k hk => (hP k).mp hk)
  omega

/-- In the original contained-L₁ branch, the natural binary linear degree is at most four. -/
theorem natural_dimension_le_four_of_one_le {n : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin n → ZMod 2))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation n) eK) : n ≤ 4 := by
  by_contra hn
  exact section_rank_bound_impossible d hH hKH hL₁K ρ hρ hcentral
    (natural_section_point_rank H V₃ V₁ K ρ hKH (by omega) eK hmodel)

/-- The same degree restriction for the determinant-one model and its prescribed quotient map. -/
theorem specialLinear_dimension_le_four_of_one_le {n : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH
      (specialLinearNatural n) eK) : n ≤ 4 := by
  by_contra hn
  exact section_rank_bound_impossible d hH hKH hL₁K ρ hρ hcentral
    (specialLinear_section_point_rank H V₃ V₁ K ρ hKH (by omega) eK hmodel)

/-- The original component section cannot be the exterior square of the binary SL₅ natural module. -/
theorem not_exterior_square_of_one_le
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group) :
    ¬ HasSectionModel H V₃ V₁ ρ K hKH (SL5TenDimensional.exteriorAction 2) eK := by
  intro hmodel
  exact section_rank_bound_impossible d hH hKH hL₁K ρ hρ hcentral
    (exterior_square_section_point_rank H V₃ V₁ K ρ hKH eK hmodel)

/-- The actual dual branch, the exterior cube, is excluded on the same original section. -/
theorem not_exterior_cube_of_one_le
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group) :
    ¬ HasSectionModel H V₃ V₁ ρ K hKH (SL5TenDimensional.exteriorAction 3) eK := by
  intro hmodel
  exact section_rank_bound_impossible d hH hKH hL₁K ρ hρ hcentral
    (exterior_cube_section_point_rank H V₃ V₁ K ρ hKH eK hmodel)

/-- Original13.7.6(2) in the contained-L₁ branch, with the irreducible model classification discharged. -/
theorem not_irreducible_ten_of_one_le
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group E) [Representation.IsIrreducible σ]
    (hdim : Module.finrank (ZMod 2) E = 10)
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group) :
    ¬ HasSectionModel H V₃ V₁ ρ K hKH σ eK := by
  intro hmodel
  exact section_rank_bound_impossible d hH hKH hL₁K ρ hρ hcentral
    (irreducible_ten_section_point_rank H V₃ V₁ K ρ hKH σ hdim eK hmodel)

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
