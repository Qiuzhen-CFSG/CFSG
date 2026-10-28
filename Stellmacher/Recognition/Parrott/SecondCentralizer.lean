module

public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Stellmacher.Recognition.Parrott.SecondCentralizerFromLocalData

/-!
# Parrott's second involution centralizer

For every supplied normalizer-fusion configuration, the centralizer of its
chosen involution v lies in the same N = N_G(F). It has order 1536, its
actual two-core is the ambient image of Ω₁(O₂(N)) of order 256, and its
quotient by that core is S₃. Involutions outside the core are conjugate to v,
with conjugators retained in C_G(z) ∨ (N).

The normalizer configuration supplies the strict Sylow containment and the
derived-core fixed-point containment required by the local-data theorem.
That theorem proves both transfer steps and ambient containment. We also
retain the Sylow intersection, its center, and an outside-core involution
whose centralizer is an elementary group of order 32 conjugate to F.
The existence theorem starts with only the original simple nonsolvable
N₂-group and Parrott centralizer hypotheses; no witnesses are replaced when
extending an already supplied configuration.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683, Lemma 8.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

set_option quotPrecheck false in
local notation "N" => normalizer (d.F : Set G)
set_option quotPrecheck false in
local notation "K" => pCore 2 N
set_option quotPrecheck false in
local notation "C" => centralizer ({n.v} : Set G)
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "P" => ((d.sylow : Subgroup G) ⊓ C : Subgroup G)
set_option quotPrecheck false in
local notation "W" => (omega₁ K (p := 2)).map ((N).subtype.comp (K).subtype)

/-- The actual second centralizer, attached to the supplied F, N, Q, and v.
All core and local-centralizer comparisons use literal ambient inclusions. -/
public structure ParrottSecondCentralizerData : Prop where
  le_normalizer : C ≤ N
  local_image_eq : ((C).subgroupOf N).map (N).subtype = C
  card : Nat.card C = 1536
  core_eq : (pCore 2 C).map (C).subtype = W
  core_card : Nat.card (pCore 2 C) = 256
  quotient : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))
  outside_core_fusion : ∀ u : G, u ∈ C → orderOf u = 2 →
    u ∉ (pCore 2 C).map (C).subtype → IsConj n.v u
  outside_core_fusion_in_join : ∀ u : G, u ∈ C → orderOf u = 2 →
    u ∉ (pCore 2 C).map (C).subtype →
      ∃ l : (H ⊔ N : Subgroup G), (l : G) * n.v * (l : G)⁻¹ = u
  original_centralizer_card : Nat.card (H ⊓ C : Subgroup G) = 512
  sylow_card : Nat.card P = 512
  sylow_center : (center P).map (P).subtype = zpowers z ⊔ zpowers n.v
  sylow_position : ∃ S : Sylow 2 C, (S : Subgroup C).map (C).subtype = P
  outer_involution : ∃ w : G, w ∈ C ∧ orderOf w = 2 ∧
    w ∉ (pCore 2 C).map (C).subtype ∧
    let B := C ⊓ centralizer ({w} : Set G)
    IsElementaryAbelian 2 B ∧ Nat.card B = 32 ∧
      ∃ a : H, d.F.map (MulAut.conj (a : G)).toMonoidHom = B

namespace ParrottNormalizerFusionData

variable [Finite G]

/-- The two transfer steps identify the ambient centralizer for this exact
normalizer configuration. All local hypotheses are discharged by its fields. -/
public theorem second_centralizer_le_normalizer
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) : C ≤ N := by
  exact d.second_centralizer_le_normalizer_of_local_data h hN
    n.sylow_lt_normalizer n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed

/-- Extend a compatible normalizer configuration by its actual second
centralizer and the local involution geometry, without choosing a new v. -/
public theorem second_centralizer_data
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    ParrottSecondCentralizerData n := by
  obtain ⟨hCN, hcard, hcore, hcorecard, hquot, hfusion⟩ :=
    d.second_centralizer_identification_of_local_data h hN n.sylow_lt_normalizer
      n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed
  refine {
    le_normalizer := hCN
    local_image_eq := map_subgroupOf_eq_of_le hCN
    card := hcard
    core_eq := hcore
    core_card := hcorecard
    quotient := hquot
    outside_core_fusion := hfusion
    outside_core_fusion_in_join := ?_
    original_centralizer_card := d.supplied_fixed_original_centralizer_card h hN
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
    sylow_card := d.normalizer_fixed_sylow_card h hN n.sylow_lt_normalizer
      n.Q n.v n.v_order n.elementary_fixed
    sylow_center := d.normalizer_fixed_sylow_center h hN n.sylow_lt_normalizer
      n.Q n.v n.v_order n.elementary_fixed
    sylow_position := d.normalizer_fixed_sylow_ambient_position h hN
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
    outer_involution := ?_ }
  · intro u hu hu2 huCore
    exact d.normalizer_fixed_outside_omega_fusion h hN n.sylow_lt_normalizer
      n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed
      u ⟨hCN hu, hu⟩ hu2 (by rwa [← hcore])
  · obtain ⟨w, hw, hw2, hwW, helem, hwcard, hconj, _⟩ :=
      d.normalizer_fixed_outer_geometry h hN n.sylow_lt_normalizer
        n.Q n.v n.v_order n.elementary_fixed
    have hNC : N ⊓ C = C := inf_eq_right.mpr hCN
    refine ⟨w, hw.2, hw2, ?_, ?_, ?_, ?_⟩
    · rwa [hcore]
    · rw [hNC] at helem
      exact helem
    · simpa only [hNC] using hwcard
    · simpa only [hNC] using hconj

end ParrottNormalizerFusionData

/-- Every supplied second elementary configuration extends to compatible
normalizer-fusion and second-centralizer data under the original hypotheses. -/
public theorem ParrottSecondElementaryData.exists_second_centralizer
    [Finite G] [IsSimpleGroup G] (d : ParrottSecondElementaryData z)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ n : ParrottNormalizerFusionData d, ParrottSecondCentralizerData n := by
  obtain ⟨n⟩ := d.exists_normalizer_fusion hns hN h
  exact ⟨n, n.second_centralizer_data h hN⟩

/-- The second-centralizer configuration exists from the original finite
nonsolvable simple N₂-group and Parrott centralizer hypotheses alone. -/
public theorem parrott_second_centralizer_exists [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ (d : ParrottSecondElementaryData z) (n : ParrottNormalizerFusionData d),
      ParrottSecondCentralizerData n := by
  obtain ⟨d, ⟨n⟩⟩ := parrott_normalizer_fusion_exists hns hN h
  exact ⟨d, n, n.second_centralizer_data h hN⟩

end Stellmacher.Recognition
