module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneStabilizers
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.AlternatingPointRanks

/-!
# The original alternating degree bound and seven-letter point

The actual source plane has a vector surviving in the component section.
Its cubic stabilizer lifts to C_G(V₂), whose earlier source three-rank is
at most one. The concrete alternating bounds therefore give degree at
most seven; in degree seven the original plane vector is a pair vector.
Both conclusions retain the original K/O₂(K) equivalence and quotient
representatives. No point nonzeroness or model stabilizer bound is assumed.

Source: Aschbacher–Smith, 13.7.6(3), printed pp.938–939, the L₁≤K branch.
The genuine earlier rank input is 13.5.4(3), produced by
Section05.AmbientSource.SourcePlaneBounds.source_plane_core_and_rank.
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

/-- The alternating natural section in the original contained branch has degree at most seven. -/
theorem alternating_degree_le_seven_of_one_le {n : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) eK) : n ≤ 7 := by
  by_contra hn
  obtain ⟨v, hv⟩ := exists_plane_section_nonzero d hKH hL₁K ρ hρ
  let hu := plane_vector_mem_commutator d hKH hL₁K ρ hρ v
  obtain ⟨hs, P, hrank, hP⟩ := alternating_large_section_point_rank H V₃ V₁ K ρ hKH
    (by omega) eK hmodel ⟨_, hu⟩
  have hHN : H ≤ normalizer (V₁ : Set G) := d.first_normalizer ▸ hH.2.1
  have hr := section_point_rank_le_plane_centralizer d hHN hKH ρ hρ v hu hv hs P
    (fun k hk => (hP k).mp hk)
  omega

/-- An original plane representative has the literal seven-letter pair marking. -/
theorem seven_plane_pair_of_one_le
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) eK) :
    ∃ v : V₂,
      let u : commutatorImage H V₃ V₁ K :=
        ⟨seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩,
          plane_vector_mem_commutator d hKH hL₁K ρ hρ v⟩
      (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0 ∧
        HasSevenPairPoint H V₃ V₁ K ρ hKH eK u := by
  obtain ⟨v, hv⟩ := exists_plane_section_nonzero d hKH hL₁K ρ hρ
  let hu := plane_vector_mem_commutator d hKH hL₁K ρ hρ v
  refine ⟨v, hv, ?_⟩
  rcases seven_pair_or_section_point_rank H V₃ V₁ K ρ hKH eK hmodel ⟨_, hu⟩ hv with hp | hb
  · exact hp
  · obtain ⟨hs, P, hrank, hP⟩ := hb
    have hHN : H ≤ normalizer (V₁ : Set G) := d.first_normalizer ▸ hH.2.1
    have hr := section_point_rank_le_plane_centralizer d hHN hKH ρ hρ v hu hv hs P
      (fun k hk => (hP k).mp hk)
    omega

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
