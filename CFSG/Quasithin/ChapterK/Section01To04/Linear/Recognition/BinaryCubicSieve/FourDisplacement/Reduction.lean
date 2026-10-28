module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Support
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Graph
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RootDisplacement

/-!
# The two remaining SL₄ displacement families

The positive-root-preserving diagram reversal reduces the final adjacent pair
to the initial pair. Every support of size at least two is either adjacent or
exactly the endpoint pair. Consequently the initial-adjacent estimate, its
application to the diagram twist, and the endpoint estimate imply the full
multiple-support contract. A second reduction removes rank-one actors
containing a component conjugate of the adjacent central root, using the
proved four-dimensional displacement image.

`InitialAdjacentDisplacement` and `EndpointDisplacement` are explicit remaining
proof obligations. Neither is claimed here. The initial-adjacent contract
allows the third root to be active and retains arbitrary outer actors.

Source: Aschbacher–Smith, K.3.2, printed pp.454–455; GM author manuscript,
Propositions 4.7–4.8 and endpoint-pair Lemma 4.5.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The remaining common-fixed-space estimate for the initial adjacent roots.
The third root is allowed to be active, so this includes full support. -/
def InitialAdjacentDisplacement (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ (J : Finset (Fin 3)) (v : V), v ≠ 0 → LocalHighestVector σ J v →
    0 ∈ J → 1 ∈ J → ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- The separate endpoint-pair estimate. In the source this is the adjoint
branch, including its outer-actor calculation. -/
def EndpointDisplacement (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ (v : V), v ≠ 0 → LocalHighestVector σ {0, 2} v →
    ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- The root calculation removes every rank-one actor containing a component
conjugate of the central root. A proof of the remaining actor configurations
therefore completes the initial-adjacent branch. -/
theorem initial_adjacent_displacement_of_remaining_actors
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) Group V)
    (hremaining : ∀ (J : Finset (Fin 3)) (v : V), v ≠ 0 →
      LocalHighestVector σ J v → 0 ∈ J → 1 ∈ J →
      ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A → rank A ≤ 4 →
      (2 ≤ rank A ∨ ∀ c : Group,
        componentEmbedding σ (c * adjacentCentralRoot 0 1 * c⁻¹) ∉ A) →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A) :
    InitialAdjacentDisplacement σ := by
  intro J v hv hJ h0 h1 A hA hc hr
  by_cases htwo : 2 ≤ rank A
  · exact hremaining J v hv hJ h0 h1 A hA hc hr (Or.inl htwo)
  · by_cases hroot : ∃ c : Group,
        componentEmbedding σ (c * adjacentCentralRoot 0 1 * c⁻¹) ∈ A
    · obtain ⟨c, hc⟩ := hroot
      exact strict_gap_of_conjugate_adjacentCentralRoot_mem_rank_le_one
        hJ hv h0 h1 (by decide) A c hc (by omega)
    · apply hremaining J v hv hJ h0 h1 A hA hc hr
      exact Or.inr (fun c hc => hroot ⟨c, hc⟩)

/-- Exhaust the multiple supports by the two adjacent pairs and the endpoint
pair. The graph twist transports the final adjacent pair, with all actors
retained in the identical linear normalizer. -/
theorem multiple_support_displacement_of_root_estimates
    (σ : Representation (ZMod 2) Group V)
    (hleft : InitialAdjacentDisplacement σ)
    (hright : InitialAdjacentDisplacement (diagramTwist σ))
    (hend : EndpointDisplacement σ) : FourMultipleSupportDisplacement σ := by
  intro J v hv hJ hcard
  by_cases h1 : (1 : Fin 3) ∈ J
  · by_cases h0 : (0 : Fin 3) ∈ J
    · exact hleft J v hv hJ h0 h1
    · have h2 : (2 : Fin 3) ∈ J := by
        by_contra h2
        have hsub : J ⊆ {1} := by
          intro i hi
          fin_cases i <;> simp_all
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      apply (actor_gap_diagramTwist_iff σ).mp
      apply hright (J.image Fin.rev) v hv (localHighestVector_diagramTwist hJ)
      · exact Finset.mem_image.mpr ⟨2, h2, rfl⟩
      · exact Finset.mem_image.mpr ⟨1, h1, rfl⟩
  · have he : J = {0, 2} := by
      have hsub : J ⊆ {0, 2} := by
        intro i hi
        fin_cases i <;> simp_all
      apply Finset.eq_of_subset_of_card_le hsub
      simpa using hcard
    subst J
    exact hend v hv hJ

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
