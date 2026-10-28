module

public import Stellmacher.Recognition.Parrott.NormalizerCoreAbelianization
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreAbelianization`.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The local quotient of order four detects a square outside the derived core. -/
public theorem normalizer_core_exists_square_not_mem_derived_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∃ x : G, x ∈ X ∧ x ^ 2 ∉ (commutator X).map X.subtype := by
  intro N X
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator_of_local_inputs h hlocal hproper
  have htZ : t ∈ (center (pCore 2 N)).map (N.subtype.comp (pCore 2 N).subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC := d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz
  change X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) at hXC
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  obtain ⟨y, hy, hy4⟩ := d.t_centralizer_exists_quotient_order_four h t ht.1 htz hCcard
  have hyX : (y : G) ∈ X := by
    rw [hXC]
    exact hy
  refine ⟨y, hyX, ?_⟩
  intro hyD
  have hyJ := d.sylow_subgroup_commutator_le_core h X d.normalizer_core_le_sylow hyD
  obtain ⟨a, ha, heq⟩ := hyJ
  have hy2 : y ^ 2 ∈ J := by
    have heq' : a = y ^ 2 := H.subtype_injective heq
    exact heq' ▸ ha
  have hpow : (QuotientGroup.mk' J y) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hy2
  have hh := orderOf_dvd_of_pow_eq_one hpow
  rw [hy4] at hh
  norm_num at hh

/-- The intrinsic core has a nontrivial square in its abelianization. -/
public theorem normalizer_core_exists_square_not_mem_native_derived_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ k : K, k ^ 2 ∉ commutator K := by
  intro N K
  obtain ⟨x, hx, hx2⟩ := d.normalizer_core_exists_square_not_mem_derived_of_local_inputs h hlocal hproper
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨⟨n, hn⟩, ?_⟩
  intro hk
  apply hx2
  rw [← d.normalizer_core_native_derived_image]
  exact mem_map_of_mem (N.subtype.comp K.subtype) hk

/-- A derived core of order 64 gives an intrinsic abelianization of order 16. -/
public theorem normalizer_core_abelianization_card_of_derived_card_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    Nat.card D = 64 →
      Nat.card (commutator K) = 64 ∧ Nat.card (Abelianization K) = 16 := by
  intro N K X D hD
  have hK : Nat.card K = 1024 := (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  have hc : Nat.card (commutator K) = 64 := by
    rw [← card_map_of_injective (K := commutator K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective), d.normalizer_core_native_derived_image]
    exact hD
  refine ⟨hc, ?_⟩
  have hh := (commutator K).index_mul_card
  change Nat.card (Abelianization K) * Nat.card (commutator K) = Nat.card K at hh
  rw [hc, hK] at hh
  omega

end Stellmacher.Recognition.ParrottSecondElementaryData
