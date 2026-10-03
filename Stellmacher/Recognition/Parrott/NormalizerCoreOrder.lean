module

public import Stellmacher.Recognition.Parrott.NormalizerCoreLowerBound
public import Stellmacher.Recognition.Parrott.NormalizerCenterBounds
public import Theory.GroupTheory.NormalSubgroupConjugacyBound
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Order and two-core quotient of the second elementary normalizer

For the supplied second elementary subgroup F, let N=N_G(F) and K=O₂(N).
The linear action bound gives |K|≥512, so the local center bound gives
|Z(K)|≤4. The orbit of the original involution in Z(K) has odd length
[N:T]>1. It therefore has length three, and |Z(K)|=4. Since |Z(T)|=2,
K is proper in T. The action on the three cosets of T identifies N/K
with S₃, giving |N|=6144 and |K|=1024.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the deductions preceding and in Lemma 6. Proper containment T<N
is an explicit input, supplied by the separate fusion argument.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The order and quotient conclusions of Lemma 6 for the actual supplied F.
The N₂ condition and local centralizer hypotheses suffice once T<N is known. -/
public theorem normalizer_core_order (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    Nat.card N = 6144 ∧ Nat.card K = 1024 ∧
      Nonempty ((N ⧸ K) ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (center K) = 4 := by
  classical
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let T := d.sylow.subtype d.sylow_le_normalizer
  let Z := (center K).map K.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let zN : N := ⟨z, d.sylow_le_normalizer (d.le_sylow d.z_mem_inf.2)⟩
  have hzZ : zN ∈ Z := by
    obtain ⟨k, hk, heq⟩ := d.z_mem_normalizer_core_center
    exact ⟨k, hk, N.subtype_injective heq⟩
  have hz1 : zN ≠ 1 := by
    intro heq
    have hz : z = 1 := congrArg N.subtype heq
    have ho := h.involution
    simp [hz] at ho
  have hcentral : centralizer ({zN} : Set N) = (T : Subgroup N) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change x * zN = zN * x ↔ (x : G) ∈ (d.sylow : Subgroup G)
    rw [Subtype.ext_iff]
    change (x : G) * z = z * (x : G) ↔ _
    rw [← mem_centralizer_singleton_iff, ← d.normalizer_inf_centralizer h]
    exact (and_iff_right x.property).symm
  have hTcard : Nat.card (T : Subgroup N) = 2048 := by
    change Nat.card ((d.sylow : Subgroup G).subgroupOf N) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe d.sylow_le_normalizer).toEquiv]
    exact d.sylow_card h
  obtain ⟨n, hnodd, _, _, hNcard, _⟩ := d.normalizer_card h
  have hindex : (T : Subgroup N).index = n := by
    have hc := (T : Subgroup N).index_mul_card
    rw [hTcard, hNcard] at hc
    omega
  have hn : 1 < n := by
    have hlt : Nat.card (d.sylow : Subgroup G) < Nat.card N := by
      apply lt_of_not_ge
      intro hc
      exact hproper.ne (eq_of_le_of_card_ge hproper.le hc)
    rw [d.sylow_card h, hNcard] at hlt
    omega
  have horbit : n < Nat.card (center K) := by
    have hh := centralizer_index_lt_card_normal Z zN hzZ hz1
    rwa [hcentral, hindex, card_map_of_injective K.subtype_injective] at hh
  have hcenterBound := d.normalizer_core_center_card_le_four h (d.normalizer_core_card_ge h hN)
  have hn3 : n = 3 := by
    obtain ⟨r, hr⟩ := hnodd
    change Nat.card (center K) ≤ 4 at hcenterBound
    omega
  have hcenter : Nat.card (center K) = 4 := by
    change Nat.card (center K) ≤ 4 at hcenterBound
    omega
  have hN6144 : Nat.card N = 6144 := by rw [hNcard, hn3]
  have hKT : K < (T : Subgroup N) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal T) ?_
    intro heq
    have hc : Nat.card (center (T : Subgroup N)) = 2 := by
      change Nat.card (center ((d.sylow : Subgroup G).subgroupOf N)) = _
      rw [Nat.card_congr (Subgroup.centerCongr
        (subgroupOfEquivOfLe d.sylow_le_normalizer)).toEquiv]
      exact d.sylow_center_card h
    have hcc := Nat.card_congr (Subgroup.centerCongr
      (MulEquiv.subgroupCongr heq)).toEquiv
    exact (by decide : (4 : ℕ) ≠ 2) (hcenter.symm.trans (hcc.trans hc))
  obtain ⟨e⟩ := sylow_index_three_core_quotient T (hindex.trans hn3) hKT
  have hquot : Nat.card (N ⧸ K) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hK1024 : Nat.card K = 1024 := by
    have hc := K.index_mul_card
    change Nat.card (N ⧸ K) * Nat.card K = Nat.card N at hc
    rw [hquot, hN6144] at hc
    omega
  exact ⟨hN6144, hK1024, ⟨e⟩, hcenter⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
