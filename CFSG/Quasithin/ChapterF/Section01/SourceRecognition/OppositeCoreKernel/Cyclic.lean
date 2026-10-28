module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.OppositeCoreKernel.Central
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Cyclic opposite-core kernels satisfy the source order bound

Suppose the literal normal core K of O₂(B) inside A is cyclic. Choose
b in B so that the two original common-Sylow conjugates generate B.
The intersection K∩Kᵇ is characteristic in both cyclic subgroups, hence
normalized by A and Aᵇ. Those two vertices generate G, so the common
normal two-core makes the intersection trivial. The two conjugates lie
in O₂(B), and their product again gives |K|²≤|O₂(B)|. Consequently
6|K|≤[A:K]≤48 and the original vertex order is at most384.

The literal quotient consumer preserves G→G/O₂(G). The final results
reduce any larger faithful source pair to noncyclic kernels on both sides,
of order at least64,32,or16 at index12,24,or48, respectively. Combined
with the central-kernel exclusion, only noncentral, noncyclic cases remain.
No complete amalgam classification or general kernel-size bound is assumed.

Source: the degree-three faithful amalgam of Aschbacher–Smith F.1.12
and F.6.5, printed pp.262–264 and305, citing Goldschmidt,
Automorphisms of trivalent graphs, Annals111(1980),377–406.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF

private theorem cyclic_characteristic {H : Type*} [Group H] [IsCyclic H]
    (K : Subgroup H) : K.Characteristic := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic H)
  obtain ⟨n, rfl⟩ := (Subgroup.le_zpowers_iff g K).mp (by rw [hg]; exact le_top)
  apply Subgroup.characteristic_iff_map_le.mpr
  intro φ
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le, map_pow]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top (φ g))
  change (φ g) ^ n ∈ Subgroup.zpowers (g ^ n)
  rw [← hi]
  have he : (g ^ i) ^ n = (g ^ n) ^ i := by
    rw [← zpow_natCast (g ^ i), ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast]
  rw [he]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

private theorem cyclic_subgroup_normalizer_mono {G : Type*} [Group G]
    (U D : Subgroup G) [IsCyclic U] (hDU : D ≤ U) :
    normalizer (U : Set G) ≤ normalizer (D : Set G) := by
  let : (D.subgroupOf U).Characteristic := cyclic_characteristic _
  have hh := normalizer_le_normalizer_characteristic_image U (D.subgroupOf U)
  rwa [map_subgroupOf_eq_of_le hDU] at hh

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- A cyclic subgroup normal in the original vertex and contained in the
opposite core has a disjoint conjugate inside that same core. -/
theorem IsGoldschmidtTriple.cyclic_subgroup_disjoint_opposite_conjugate
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (U : Subgroup G) [IsCyclic U]
    (hu : U ≤ (pCore 2 B).map B.subtype)
    (hn : A ≤ normalizer (U : Set G)) :
    ∃ b : B, Disjoint U (U.map (MulAut.conj (b : G)).toMonoidHom) ∧
      U.map (MulAut.conj (b : G)).toMonoidHom ≤ (pCore 2 B).map B.subtype := by
  obtain ⟨b,hb⟩ := h.exists_right_generating_sylow_conjugate
  let f := (MulAut.conj (b : G)).toMonoidHom
  let U' := U.map f
  let D := U ⊓ U'
  have he : U ≃* U' := U.equivMapOfInjective f (MulAut.conj (b : G)).injective
  let : IsCyclic U' := he.isCyclic.mp inferInstance
  have hAD : A ≤ normalizer (D : Set G) :=
    hn.trans (cyclic_subgroup_normalizer_mono U D inf_le_left)
  have hAn : A.map f ≤ normalizer (U' : Set G) :=
    (map_mono (f := f) hn).trans (le_normalizer_map f)
  have hA'D : A.map f ≤ normalizer (D : Set G) :=
    hAn.trans (cyclic_subgroup_normalizer_mono U' D inf_le_right)
  have hBD : B ≤ normalizer (D : Set G) := by
    rw [← hb]
    exact sup_le (inf_le_left.trans hAD)
      ((map_mono (f := f) (show A ⊓ B ≤ A from inf_le_left)).trans hA'D)
  have hDT : D ≤ A ⊓ B := inf_le_left.trans (hu.trans
    (by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection))
  have hbot : D = ⊥ := h.common_normal_eq_bot hcore D hDT
    (normal_subgroupOf_of_le_normalizer hAD) (normal_subgroupOf_of_le_normalizer hBD)
  refine ⟨b,disjoint_iff.mpr hbot,?_⟩
  have hnormal := h.symm.left_core_normalized b.property
  have heq := mem_normalizer_iff_map_conj_eq.mp hnormal
  exact (map_mono (f := f) hu).trans heq.le

/-- Counting the two literal disjoint cyclic conjugates inside the opposite core. -/
theorem IsGoldschmidtTriple.cyclic_subgroup_card_sq_le_opposite_core
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (U : Subgroup G) [IsCyclic U]
    (hu : U ≤ (pCore 2 B).map B.subtype)
    (hn : A ≤ normalizer (U : Set G)) :
    Nat.card U ^ 2 ≤ Nat.card (pCore 2 B) := by
  obtain ⟨b,hd,hb⟩ := h.cyclic_subgroup_disjoint_opposite_conjugate hcore U hu hn
  let U' := U.map (MulAut.conj (b : G)).toMonoidHom
  have hUA : U' ≤ A := hb.trans (h.symm.local_twoCore_le_intersection.trans inf_le_right)
  have he : Nat.card U' = Nat.card U := card_map_of_injective (MulAut.conj (b : G)).injective
  have hp := card_sup_eq_mul_of_normalizes_of_disjoint U U' (hUA.trans hn) hd
  have hle := card_le_of_le (sup_le hu hb)
  rw [hp,he,card_map_of_injective B.subtype_injective] at hle
  simpa only [pow_two] using hle

/-- A cyclic literal degree-six kernel satisfies the weighted order bound. -/
theorem IsGoldschmidtTriple.cyclic_opposite_kernel_weighted_bound
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    [IsCyclic (((pCore 2 B).map B.subtype).subgroupOf A).normalCore] :
    6 * Nat.card (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤
      (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.index := by
  let R := ((pCore 2 B).map B.subtype).subgroupOf A
  let K := R.normalCore
  let U := K.map A.subtype
  let : IsCyclic U := (K.equivMapOfInjective A.subtype A.subtype_injective).isCyclic.mp inferInstance
  have hu : U ≤ (pCore 2 B).map B.subtype := by
    rintro x ⟨y,hy,rfl⟩
    exact R.normalCore_le hy
  have hn : A ≤ normalizer (U : Set G) := by
    have hh := K.le_normalizer_map A.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hsq := h.cyclic_subgroup_card_sq_le_opposite_core hcore U hu hn
  rw [card_map_of_injective A.subtype_injective] at hsq
  have hcard := K.index_mul_card
  rw [show Nat.card A = Nat.card B by
    rw [h.local_card_eq_three_mul_intersection,h.symm.local_card_eq_three_mul_intersection,
      inf_comm B A],SymmetricThreeTwoCore.card_eq h.quotient_right.some] at hcard
  have hp := Nat.card_pos (α := K)
  change 6 * Nat.card K ≤ K.index
  nlinarith

/-- Cyclicity, with no assumed kernel-size bound, gives the original 384 bound. -/
theorem IsGoldschmidtTriple.local_cards_le_384_of_cyclic_opposite_kernel
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    [IsCyclic (((pCore 2 B).map B.subtype).subgroupOf A).normalCore] :
    Nat.card A ≤ 384 ∧ Nat.card B ≤ 384 ∧ Nat.card (A ⊓ B : Subgroup G) ≤ 128 := by
  have hw := h.cyclic_opposite_kernel_weighted_bound hcore
  have hi := Nat.le_of_dvd (by decide : 0 < 48)
    h.opposite_core_normalCore_index_dvd_forty_eight
  apply h.local_cards_le_384_of_oriented_kernel_bounds
  exact Or.inl (Or.inr (Or.inr (by omega)))

/-- Larger source pairs have noncyclic kernels in both orientations. -/
theorem IsGoldschmidtTriple.both_opposite_kernels_noncyclic_of_large_vertex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hlarge : 384 < Nat.card A) :
    ¬ IsCyclic (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ∧
    ¬ IsCyclic (((pCore 2 A).map A.subtype).subgroupOf B).normalCore := by
  constructor
  · intro hc
    let _ := hc
    exact (not_lt_of_ge (h.local_cards_le_384_of_cyclic_opposite_kernel hcore).1) hlarge
  · intro hc
    let _ := hc
    exact (not_lt_of_ge (h.symm.local_cards_le_384_of_cyclic_opposite_kernel hcore).2.1) hlarge


/-- The cyclic-kernel branch retains the literal quotient images and overlap. -/
theorem IsGoldschmidtTriple.quotient_local_cards_le_384_of_cyclic_opposite_kernel
    (h : IsGoldschmidtTriple A B)
    (hc :
      let q := QuotientGroup.mk' (pCore 2 G)
      let A' := A.map q
      let B' := B.map q
      IsCyclic (((pCore 2 B').map B'.subtype).subgroupOf A').normalCore) :
    let q := QuotientGroup.mk' (pCore 2 G)
    Nat.card (A.map q) ≤ 384 ∧ Nat.card (B.map q) ≤ 384 ∧
      Nat.card ((A ⊓ B).map q) ≤ 128 := by
  let _ := hc
  have hh := h.quotient_twoCore.local_cards_le_384_of_cyclic_opposite_kernel
    h.quotient_twoCore_eq_bot
  rw [← h.quotient_twoCore_intersection] at hh
  exact hh

/-- The correctly weighted kernel orders in every remaining counterexample.
Together with the two preceding branch exclusions, these are noncentral,
noncyclic kernels of order at least16,32,or64 in the stated index cases. -/
theorem IsGoldschmidtTriple.large_vertex_opposite_kernel_lower_bounds
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting B = pCore 2 B) (hlarge : 384 < Nat.card A) :
    let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
    (K.index = 12 ∧ 64 ≤ Nat.card K) ∨
      (K.index = 24 ∧ 32 ≤ Nat.card K) ∨
      (K.index = 48 ∧ 16 ≤ Nat.card K) := by
  let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
  have hK : IsPGroup 2 K := pCore_isPGroup.to_le h.opposite_core_normalCore_le_twoCore
  obtain ⟨n,hn⟩ := hK.exists_card_eq
  have hc := K.index_mul_card
  rcases h.opposite_kernel_index_cases hcore hgood with h12 | h24 | h48
  · refine Or.inl ⟨h12,?_⟩
    change K.index = 12 at h12
    rw [h12,hn] at hc
    have hn6 : 6 ≤ n := by
      by_contra hh
      have hb : 2 ^ n ≤ 32 := by
        exact (Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 5 by omega))
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn6
  · refine Or.inr (Or.inl ⟨h24,?_⟩)
    change K.index = 24 at h24
    rw [h24,hn] at hc
    have hn5 : 5 ≤ n := by
      by_contra hh
      have hb : 2 ^ n ≤ 16 := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 4 by omega)
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn5
  · refine Or.inr (Or.inr ⟨h48,?_⟩)
    change K.index = 48 at h48
    rw [h48,hn] at hc
    have hn4 : 4 ≤ n := by
      by_contra hh
      have hb : 2 ^ n ≤ 8 := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 3 by omega)
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn4

end CFSG.Quasithin.ChapterF
