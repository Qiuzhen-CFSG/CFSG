module

public import Stellmacher.Recognition.Parrott.SecondCentralizer
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.OuterGeometry

/-!
# The full second-centralizer data once ambient containment is established

The local-input calculation identifies C_N(v), its actual two-core and S₃
quotient. Containment C_G(v) ≤ N_G(F) transports those identities to the full
centralizer. The outside-core fusion, original-centralizer intersection,
Sylow center and outer-involution geometry use the same supplied F and v.

Only ambient containment remains explicit. Its source producer must discharge
it using the two transfers and the quotient-centralizer calculation. No global
N₂ hypothesis or solvability of C_G(v) is used here.

Source: Parrott (1972), Lemma 8, printed pp.682–683.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Transfer the proved local order, actual core, and quotient along an
established ambient centralizer containment. -/
public theorem second_centralizer_structure_of_containment_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v)
    (hcontain : centralizer ({v} : Set G) ≤ normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let C := centralizer ({v} : Set G)
    Nat.card C = 1536 ∧
      (pCore 2 C).map C.subtype = (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 C) = 256 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) := by
  intro N K C
  let B := C.subgroupOf N
  let e : B ≃* C := subgroupOfEquivOfLe hcontain
  obtain ⟨hcard, hcore, hcorecard, ⟨eqv⟩⟩ :=
    d.normalizer_fixed_centralizer_structure_of_local_inputs h hlocal hproper Q v hv hfix
  have he : (pCore 2 B).map e.toMonoidHom = pCore 2 C := pCore_map_iso 2 e
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans hcard, ?_, ?_, ?_⟩
  · rw [← he, map_map]
    change ((pCore 2 B).map B.subtype).map N.subtype = _ at hcore
    have hcomp : C.subtype.comp e.toMonoidHom = N.subtype.comp B.subtype := by
      ext x
      rfl
    rw [hcomp]
    simpa only [map_map] using hcore
  · rw [← he, card_map_of_injective e.injective]
    exact hcorecard
  · exact ⟨(QuotientGroup.congr (pCore 2 B) (pCore 2 C) e he).symm.trans eqv⟩

/-- Every involution in the local second centralizer outside omega is conjugate
to the prescribed fixed point, with a conjugator in the original-centralizer
and second-normalizer join. -/
public theorem normalizer_fixed_outside_omega_fusion_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let H := centralizer ({z} : Set G)
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ N ⊓ centralizer ({v} : Set G) → orderOf u = 2 → u ∉ W →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro N K X D A W H L hCD v hv hfix u hu hu2 huW
  obtain ⟨g, hgJ, hgE⟩ :=
    d.normalizer_fixed_outside_omega_transport_of_local_inputs h hlocal hproper Q v hv hfix u hu hu2 huW
  have hg2 : orderOf ((g : G) * u * (g : G)⁻¹) = 2 :=
    ((MulAut.conj (g : G)).orderOf_eq u).trans hu2
  obtain ⟨l, hl⟩ := d.core_involution_fusion_in_join_of_local_inputs h hlocal hproper Q hCD v hv hfix
    _ hgJ hgE hg2
  let gL : L := ⟨g, (show N ≤ L from le_sup_right) g.property.1⟩
  refine ⟨gL⁻¹ * l, ?_⟩
  change ((g : G)⁻¹ * (l : G)) * v * ((g : G)⁻¹ * (l : G))⁻¹ = u
  calc
    _ = (g : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) * (g : G) := by group
    _ = u := by rw [hl]; group

/-- Under ambient containment, the actual second two-core and quotient have
the prescribed orders and every involution outside that core is conjugate to v. -/
public theorem second_centralizer_identification_of_containment_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let C := centralizer ({v} : Set G)
    C ≤ N →
    Nat.card C = 1536 ∧
      (pCore 2 C).map C.subtype = (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 C) = 256 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      (∀ u : G, u ∈ C → orderOf u = 2 → u ∉ (pCore 2 C).map C.subtype →
        IsConj v u) := by
  intro N K X D A hCD v hv hfix C hcontain
  obtain ⟨hcard, hcore, hcorecard, hquot⟩ :=
    d.second_centralizer_structure_of_containment_of_local_inputs h hlocal hproper Q v hv hfix hcontain
  refine ⟨hcard, hcore, hcorecard, hquot, ?_⟩
  intro u hu hu2 huCore
  obtain ⟨l, hl⟩ := d.normalizer_fixed_outside_omega_fusion_of_local_inputs h hlocal hproper Q hCD v hv hfix
    u ⟨hcontain hu, hu⟩ hu2 (by rwa [← hcore])
  exact isConj_iff.mpr ⟨(l : G), hl⟩

end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

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

/-- Extend a compatible normalizer configuration by its actual second
centralizer and the local involution geometry, without choosing a new v. -/
public theorem second_centralizer_data_of_containment_of_local_inputs
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hCN : C ≤ N) :
    ParrottSecondCentralizerData n := by
  obtain ⟨hcard, hcore, hcorecard, hquot, hfusion⟩ :=
    d.second_centralizer_identification_of_containment_of_local_inputs h hlocal n.sylow_lt_normalizer
      n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed hCN
  refine {
    le_normalizer := hCN
    local_image_eq := map_subgroupOf_eq_of_le hCN
    card := hcard
    core_eq := hcore
    core_card := hcorecard
    quotient := hquot
    outside_core_fusion := hfusion
    outside_core_fusion_in_join := ?_
    original_centralizer_card := d.supplied_fixed_original_centralizer_card_of_local_inputs h hlocal
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
    sylow_card := d.normalizer_fixed_sylow_card_of_local_inputs h hlocal n.sylow_lt_normalizer
      n.Q n.v n.v_order n.elementary_fixed
    sylow_center := d.normalizer_fixed_sylow_center_of_local_inputs h hlocal n.sylow_lt_normalizer
      n.Q n.v n.v_order n.elementary_fixed
    sylow_position := d.normalizer_fixed_sylow_ambient_position_of_local_inputs h hlocal
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
    outer_involution := ?_ }
  · intro u hu hu2 huCore
    exact d.normalizer_fixed_outside_omega_fusion_of_local_inputs h hlocal n.sylow_lt_normalizer
      n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed
      u ⟨hCN hu, hu⟩ hu2 (by rwa [← hcore])
  · obtain ⟨w, hw, hw2, hwW, helem, hwcard, hconj, _⟩ :=
      d.normalizer_fixed_outer_geometry_of_local_inputs h hlocal n.sylow_lt_normalizer
        n.Q n.v n.v_order n.elementary_fixed
    have hNC : N ⊓ C = C := inf_eq_right.mpr hCN
    refine ⟨w, hw.2, hw2, ?_, ?_, ?_, ?_⟩
    · rwa [hcore]
    · rw [hNC] at helem
      exact helem
    · simpa only [hNC] using hwcard
    · simpa only [hNC] using hconj

end Stellmacher.Recognition.ParrottNormalizerFusionData
