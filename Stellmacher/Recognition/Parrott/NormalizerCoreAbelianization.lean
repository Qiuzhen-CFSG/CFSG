module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmega

/-!
# The non-elementary abelianization of the second normalizer core

The local quotient of the involution centralizer contains an element of order
four, while the derived subgroup of the second core lies in the first core.
Consequently the second core has a square outside its derived subgroup. If
that derived subgroup has order 64, the abelianization has order 16. These
facts retain the supplied elementary subgroup and the literal ambient maps.
The omega subgroup has index four, so its abelian quotient also places the
derived core inside omega.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the deductions following the calculation of K′.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The local quotient of order four detects a square outside the derived core. -/
public theorem normalizer_core_exists_square_not_mem_derived (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∃ x : G, x ∈ X ∧ x ^ 2 ∉ (commutator X).map X.subtype := by
  intro N X
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center (pCore 2 N)).map (N.subtype.comp (pCore 2 N).subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC := d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
  change X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) at hXC
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order h hN hproper).2.1
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

omit [Finite G] in
/-- Intrinsic and ambient derived cores agree under the literal subtype maps. -/
public theorem normalizer_core_native_derived_image (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    (commutator K).map (N.subtype.comp K.subtype) =
      (commutator X).map X.subtype := by
  intro N K X
  rw [map_commutator_eq, map_subtype_commutator,
    MonoidHom.range_comp, range_subtype]

/-- The intrinsic core has a nontrivial square in its abelianization. -/
public theorem normalizer_core_exists_square_not_mem_native_derived (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ k : K, k ^ 2 ∉ commutator K := by
  intro N K
  obtain ⟨x, hx, hx2⟩ := d.normalizer_core_exists_square_not_mem_derived h hN hproper
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨⟨n, hn⟩, ?_⟩
  intro hk
  apply hx2
  rw [← d.normalizer_core_native_derived_image]
  exact mem_map_of_mem (N.subtype.comp K.subtype) hk

/-- A derived core of order 64 gives an intrinsic abelianization of order 16. -/
public theorem normalizer_core_abelianization_card_of_derived_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    Nat.card D = 64 →
      Nat.card (commutator K) = 64 ∧ Nat.card (Abelianization K) = 16 := by
  intro N K X D hD
  have hK : Nat.card K = 1024 := (d.normalizer_core_order h hN hproper).2.1
  have hc : Nat.card (commutator K) = 64 := by
    rw [← card_map_of_injective (K := commutator K) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective), d.normalizer_core_native_derived_image]
    exact hD
  refine ⟨hc, ?_⟩
  have hh := (commutator K).index_mul_card
  change Nat.card (Abelianization K) * Nat.card (commutator K) = Nat.card K at hh
  rw [hc, hK] at hh
  omega

/-- The intrinsic omega subgroup has index four in the second core. -/
public theorem normalizer_core_omega_index (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    (omega₁ K (p := 2)).index = 4 := by
  intro N K
  have hc := (omega₁ K (p := 2)).index_mul_card
  rw [(d.normalizer_core_omega_structure h hN hproper).1,
    (d.normalizer_core_order h hN hproper).2.1] at hc
  omega

/-- The derived core lies in omega, since the quotient has order four. -/
public theorem normalizer_core_native_derived_le_omega (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    commutator K ≤ omega₁ K (p := 2) := by
  intro N K
  let U := omega₁ K (p := 2)
  let : U.Characteristic := omega₁_characteristic K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (K ⧸ U) = 2 ^ 2 := d.normalizer_core_omega_index h hN hproper
  let : IsMulCommutative (K ⧸ U) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
  have hh := Abelianization.commutator_subset_ker (QuotientGroup.mk' U)
  rwa [QuotientGroup.ker_mk'] at hh

end Stellmacher.Recognition.ParrottSecondElementaryData
