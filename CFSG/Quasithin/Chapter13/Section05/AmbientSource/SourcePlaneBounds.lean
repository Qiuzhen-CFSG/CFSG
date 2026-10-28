module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.PlaneBounds
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Centralizer
/-!
# The original source application of the plane bounds

Quasithinness in the counterexample bounds the actual normalizer of V₂.
The preceding normal-closure calculation therefore supplies the point-core
centralizer containment of 13.3.15(4) and the three-rank conclusion of
13.5.4(3), with the original G₁, V₂ and Sylow unchanged. The earlier
noncentrality theorem and marked cubic parabolic remain explicit inputs.
Source: Aschbacher–Smith, printed pp.893–894 and 916.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsKleinFour
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
/-- The literal point-core containment and plane-centralizer rank in the original setup. -/
theorem source_plane_core_and_rank {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H) (X : Subgroup G)
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : letI := source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅H.pCoreIn 2, E⁆ ≠ ⊥) :
    H.pCoreIn 2 ⊓ centralizer (E : Set G) ≤ (normalizer (E : Set G)).pCoreIn 2 ∧
      primeRank 3 (centralizer (E : Set G)) ≤ 1 := by
  let := source_plane_isKleinFour d
  have hm' : ⁅(normalizer (P : Set G)).pCoreIn 2,E⁆ ≠ ⊥ := d.first_normalizer ▸ hm
  have he : E ≠ ⊥ := by intro h; have hc := d.plane_card; simp [h] at hc
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 2) d.plane_card
  have hr : primeRank 3 (normalizer (E : Set G)) ≤ 2 :=
    isQuasithin_iff_twoLocal.mp d.counterexample.qtke.quasithin
      (normalizer (E : Set G)) ⟨E,he,hp,rfl⟩ 3 Nat.prime_three (by decide)
  have hc := point_core_centralizer_le_plane_cores T P E X d.line_card d.line_le_plane
    d.line_stable d.plane_stable hXN hTX hX hx hkX hm'
  constructor
  · rw [d.first_normalizer]
    exact hc.1.trans hc.2
  · exact plane_centralizer_three_rank T P E X d.line_card d.line_le_plane
      d.line_stable d.plane_stable hXN hTX hX hx hkX hm' hr
end CFSG.Quasithin.Chapter13.Section05.AmbientSource
