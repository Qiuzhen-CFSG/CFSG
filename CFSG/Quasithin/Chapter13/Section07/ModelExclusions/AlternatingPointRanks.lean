module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointStabilizerRanks
public import Theory.Representation.BinaryPermutation.PointStabilizerRank.Seven

/-!
# Alternating natural points in the original component section

The model point stabilizer pulls back through the original K/O₂(K) actor
map without changing its odd rank. In degree at least eight this always
produces rank two. In degree seven a nonzero point either does the same or
has a pair representative, retaining the given actor equivalence and all
representatives of the original commutator quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.6(3),
printed pp.938–939. The earlier-source construction and nonzeroness of the
marked point and its lift to C_K(V₂) are discharged by the model-exclusion
source assembly; they are not replaced here by a rank assumption.
-/

@[expose] public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
open BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointRanks
open Section08.TransvectionRecognition.Component
open Section08
variable {G : Type*} [Group G] [Finite G]
  (H V₃ V₁ K : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hKH : K ≤ H)

private theorem section_point_rank_at
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (hs : ∀ (k : K) (w : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w ∈ commutatorImage H V₃ V₁ K)
    (e : ComponentSection H V₃ V₁ ρ K ≃ₗ[ZMod 2] E)
    (he : ∀ (k : K) (w : commutatorImage H V₃ V₁ K),
      e (Submodule.Quotient.mk ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w,hs k w⟩) =
      σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (e (Submodule.Quotient.mk w)))
    (u : commutatorImage H V₃ V₁ K)
    (hrank : 2 ≤ primeRank 3 (representationStabilizer σ (e (Submodule.Quotient.mk u)))) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  let : Finite A := Finite.of_equiv (K ⧸ pCore 2 K) eK.toEquiv
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S := representationStabilizer σ (e (Submodule.Quotient.mk u))
  refine ⟨hs,S.comap q,?_,?_⟩
  · have hk : IsPGroup 2 q.ker := by
      have hker : q.ker = pCore 2 K := by
        dsimp only [q]
        rw [MonoidHom.ker_comp_of_injective _ _ eK.injective, QuotientGroup.ker_mk']
      rw [hker]
      exact pCore_isPGroup
    rw [primeRank_comap_eq_of_isTwoGroup_ker 3 (by decide) q
      (eK.surjective.comp (QuotientGroup.mk'_surjective _)) hk S]
    exact hrank
  · intro k
    change σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (e (Submodule.Quotient.mk u)) =
      e (Submodule.Quotient.mk u) ↔ _
    rw [← he k u, e.injective.eq_iff]

/-- The original alternating natural model cannot have degree at least eight
when its actual section point has a rank-one stabilizer. -/
theorem alternating_large_section_point_rank {n : ℕ} (hn : 8 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin n)) eK)
    (u : commutatorImage H V₃ V₁ K) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  obtain ⟨hs,e,he⟩ := hmodel
  exact section_point_rank_at H V₃ V₁ K ρ hKH _ eK hs e he u
    (BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer (by simpa using hn) _)

/-- A genuine pair marking on the actual component quotient, with the same
actor equivalence and every original representative retained. -/
def HasSevenPairPoint
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (u : commutatorImage H V₃ V₁ K) : Prop :=
  ∃ (hs : ∀ (k : K) (w : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w ∈ commutatorImage H V₃ V₁ K)
    (e : ComponentSection H V₃ V₁ ρ K ≃ₗ[ZMod 2] natural (Fin 7)),
    (∀ (k : K) (w : commutatorImage H V₃ V₁ K),
      e (Submodule.Quotient.mk ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w,hs k w⟩) =
      alternatingNaturalRepresentation (Fin 7) (eK (QuotientGroup.mk' (pCore 2 K) k))
        (e (Submodule.Quotient.mk w))) ∧
      BinaryPermutation.PointStabilizerRank.IsPairVector (e (Submodule.Quotient.mk u))

/-- The actual seven-letter model gives either the source pair point or a
rank-two stabilizer on the original K quotient representatives. -/
theorem seven_pair_or_section_point_rank
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 7)) eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    HasSevenPairPoint H V₃ V₁ K ρ hKH eK u ∨ SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  obtain ⟨hs,e,he⟩ := hmodel
  have hv : e (Submodule.Quotient.mk u) ≠ 0 :=
    fun h => hu (e.injective (h.trans (map_zero e).symm))
  rcases BinaryPermutation.PointStabilizerRank.pair_or_two_le_stabilizer _ hv with hp | hr
  · exact Or.inl ⟨hs,e,he,hp⟩
  · exact Or.inr (section_point_rank_at H V₃ V₁ K ρ hKH _ eK hs e he u hr)
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointRanks
