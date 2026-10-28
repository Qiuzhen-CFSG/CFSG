module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Structure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SeedComparison
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Seed

/-!
# The original rank-two generating seed

The flag orders give the literal index |V₃:V₁| = 4, hence dimension two
for the image of V₃ in U_H/V₁. The original point-residual orbit theorem
proves the invariant-subgroup criterion for V₃/V₁. It transports to the exact
restricted representation used in both partition branches. The original
seed commutator then generates U_H and its literal binary quotient whenever
the earlier component containment L₁ ≤ K holds. No seed irreducibility or
commutator-generation premise remains in these original-source applications.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.3(6),
the standing setup on pp.946–947, and the generating seed recalled before
13.8.22, p.957.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open TransvectionRecognition.Component.ModelExtension PairsBranch

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  [IsElementaryAbelian 2 (Source.UH H V₃)]

include d

/-- The original orders two and eight construct the exact seed index. -/
theorem source_seed_index : (V₁.subgroupOf V₃).index = 4 := by
  have h := (V₁.subgroupOf V₃).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (d.line_le_plane.trans d.plane_le_seed)).toEquiv, d.line_card, d.seed_card] at h
  omega

/-- Dimension two for the literal source image, from the original flag. -/
theorem source_seed_rank : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2 := by
  exact Components.Suzuki.NaturalSections.sourceSeed_finrank_two H V₃ V₁
    (source_seed_index d)

/-- The invariant-subgroup form of the earlier seed irreducibility supplies
the module irreducibility required by both partition consumers. -/
theorem source_seed_irreducible
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)
    (hLH : sourceOne L T V₁ ≤ H)
    (hn : sourceOne L T V₁ ≤ normalizer (V₃ : Set G))
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      sourceOne L T V₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃) :
    IsIrreducible (sourceSeed H V₃ V₁ ρ hρ (sourceOne L T V₁) hn).toRepresentation := by
  have hline : V₁ < V₃ := by
    refine lt_of_le_of_ne (d.line_le_plane.trans d.plane_le_seed) ?_
    intro he
    have hc := d.line_card
    rw [he, d.seed_card] at hc
    omega
  exact Components.Swapped.LinearTwo.ModuleAlternatives.markedSeed_irreducible
    H V₃ V₁ ρ hρ (sourceOne L T V₁) hLH hn hline hirr

open SourceCompletion
variable {K : Subgroup G}

include d in
/-- The original seed is normalized by the literal L₁T. -/
theorem source_seed_normalized :
    sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G) :=
  sup_le (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d))
    d.seed_stable

include d in
/-- Original flag transitivity supplies the irreducibility used by both partitions. -/
theorem source_seed_irreducible_original
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ) :
    IsIrreducible (sourceSeed H V₃ V₁ ρ hρ (sourceOne L T V₁)
      (le_sup_left.trans (source_seed_normalized d))).toRepresentation := by
  apply source_seed_irreducible d ρ hρ (le_sup_left.trans hH.1.2)
  exact AlternatingAndLinear.FourStructure.OriginalSource.seed_irreducible_source d
    (le_sup_left.trans hH.1.2) ρ hρ

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
include d in
/-- Full seed commutator generation gives the original component generation field. -/
theorem source_generated_original (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hLK : sourceOne L T V₁ ≤ K) :
    Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ :=
  source_generated hKH hKn hLK
    (Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d))

include d in
/-- The constructed generation identity acts on the literal quotient used by the sieve. -/
theorem source_linear_generated_original (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hLK : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ :=
  source_commutator_generated H V₃ V₁ ρ hρ K hKH (source_generated_original d hKH hKn hLK)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
