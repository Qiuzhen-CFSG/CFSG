module

public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Stellmacher.Recognition.Parrott.DerivedLocalCenters
public import Theory.GroupTheory.CentralCommutatorPairCorrection

/-!
# Correcting two marked derived elements by one core conjugation

Let H=C_G(z), J=O₂(H), and E be the literal ambient image of J′.
For the supplied normalizer data, t and v are independent modulo ⟨z⟩:
the group ⟨z,t,v⟩ is the supplied omega-center of order eight.
The centralizer pairing formula therefore gives |C_J(t,v)|=128.
Since |J|=512, the two central commutator rows J → ⟨z⟩ × ⟨z⟩
are jointly surjective. A single element of J consequently corrects
any prescribed pair of central displacements of these marked elements.

The proof preserves the original t, v, and all ambient subgroup inclusions.
Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, the central commutator pairing in properties (a)–(d).
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition
namespace ParrottNormalizerFusionData

/-- Two lifts of the marked derived elements modulo ⟨z⟩ can be corrected
simultaneously by conjugation in the actual ambient two-core. -/
public theorem exists_derived_marked_pair_correction
    {G : Type*} [Group G] [Finite G] {z : G}
    (h : ParrottCentralizerHypotheses z)
    {e : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData e) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t0 v0 : G, t0 ∈ E → v0 ∈ E →
      t0 * n.t⁻¹ ∈ zpowers z → v0 * n.v⁻¹ ∈ zpowers z →
      ∃ j : G, j ∈ J.map H.subtype ∧
        j * t0 * j⁻¹ = n.t ∧ j * v0 * j⁻¹ = n.v := by
  intro H J E t0 v0 _ht0 _hv0 ht0 hv0
  let K := J.map H.subtype
  let U := (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v
  have hKH : K ≤ H := map_subtype_le J
  have hZ : zpowers z ≤ centralizer (K : Set G) := by
    apply zpowers_le.mpr
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hKH hj)
  have hUcard : Nat.card U = 8 := by
    dsimp only [U]
    rw [← n.omega_center_eq]
    exact n.ambient_omega_center_card
  have hUE : U ≤ E := by
    dsimp only [U]
    rw [← n.omega_center_eq]
    exact n.omega_center_le_inf.trans inf_le_left
  have hC : K ⊓ centralizer (U : Set G) =
      K ⊓ centralizer ({n.t, n.v} : Set G) := by
    ext j
    constructor
    · intro hj
      refine ⟨hj.1, ?_⟩
      intro a ha
      rcases ha with rfl | ha
      · exact hj.2 n.t (mem_sup_left (mem_sup_right (mem_zpowers n.t)))
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact hj.2 n.v (mem_sup_right (mem_zpowers n.v))
    · intro hj
      have hUj : U ≤ centralizer ({j} : Set G) := by
        refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_))
          (zpowers_le.mpr ?_)
        · exact mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp (hKH hj.1)).symm
        · exact mem_centralizer_singleton_iff.mpr (hj.2 n.t (by simp))
        · exact mem_centralizer_singleton_iff.mpr (hj.2 n.v (by simp))
      exact ⟨hj.1, fun a ha => mem_centralizer_singleton_iff.mp (hUj ha)⟩
  have hCcard : Nat.card (K ⊓ centralizer ({n.t, n.v} : Set G) : Subgroup G) = 128 := by
    have hc := parrott_core_inf_centralizer_card z h U
      (le_sup_left.trans le_sup_left) hUE
    change Nat.card U * Nat.card (K ⊓ centralizer (U : Set G) : Subgroup G) = 1024 at hc
    rw [hUcard, hC] at hc
    omega
  have hKcard : Nat.card K = 512 := by
    rw [card_map_of_injective H.subtype_injective]
    exact h.core_card
  obtain ⟨hZmap, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator J, (⊤ : Subgroup J)⁆ ≤ center J := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using commutator_upperCentralSeries_top_le J 1
  have hrow (a : G) (ha : a ∈ E) (j : G) (hj : j ∈ K) : ⁅a, j⁆ ∈ zpowers z := by
    obtain ⟨aJ, haJ, rfl⟩ := ha
    obtain ⟨jH, hjJ, rfl⟩ := hj
    let embed := H.subtype.comp J.subtype
    change ⁅embed aJ, embed ⟨jH, hjJ⟩⁆ ∈ zpowers z
    rw [← map_commutatorElement, ← hZmap]
    exact mem_map_of_mem embed (hcomm (commutator_mem_commutator haJ (mem_top _)))
  apply exists_pair_conjugation_of_centralizer_card K (zpowers z) hZ n.t n.v
    (hrow n.t n.t_mem_inf.1) (hrow n.v n.v_mem_inf.1) ?_ t0 v0 ht0 hv0
  rw [hKcard, Nat.card_zpowers, h.involution, hCcard]

end ParrottNormalizerFusionData
end Stellmacher.Recognition
