module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.NormalFourCyclicSection
/-!
# Fixed points in a centralizing cyclic-four section

Let `W < H` be normal subgroups of a finite two-group, with `W` elementary
abelian. Suppose `K` centralizes `W` and has a cyclic quotient of order four
whose kernel is central in the ambient group. Every involution of `K` fixes
an element of `H` outside `W`.

Choose a normal intermediate subgroup `W ≤ X ≤ H` with `|X:W| = 2`.
Conjugation by `K` fixes both layers of `X > W > 1`, so its squares centralize
`X`. An involution in the cyclic-four quotient is a square; the central
kernel then shows that the original involution centralizes `X` as well.

This is the normal-subgroup-chain obstruction in Janko–Thompson (1970),
§4, printed p.390. Applying the chain directly in `H` also avoids having to
first estimate the subgroup `[H,t]` used in the source.
-/

namespace Subgroup

open scoped commutatorElement

private theorem normal_step (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W H : Subgroup P) [W.Normal] [H.Normal] (hWH : W < H) :
    ∃ X : Subgroup P, X.Normal ∧ W ≤ X ∧ X ≤ H ∧ W.relIndex X = 2 := by
  let q := QuotientGroup.mk' W
  let Q := P ⧸ W
  let B := H.map q
  let : B.Normal := (inferInstance : H.Normal).map q (QuotientGroup.mk'_surjective W)
  have hB : B ≠ ⊥ := by
    intro hb
    have hh := (map_eq_bot_iff H).mp hb
    rw [QuotientGroup.ker_mk'] at hh
    exact (not_le_of_gt hWH) hh
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
  have hQ : IsPGroup 2 Q := hP.to_quotient W
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  obtain ⟨n, hn⟩ := (hQ.to_subgroup B).exists_card_eq
  have hnpos : 1 ≤ n := by
    have hp : 1 < Nat.card B := Finite.one_lt_card
    by_contra hh
    have : n = 0 := by omega
    rw [hn, this] at hp
    norm_num at hp
  obtain ⟨Y, hYn, hYB, hYc⟩ :=
    exists_normal_subgroup_card_pow_of_normal B inferInstance hn 1 hnpos
  let : Y.Normal := hYn
  let X := Y.comap q
  have hWX : W ≤ X := by
    intro w hw
    change q w ∈ Y
    rw [show q w = 1 from (QuotientGroup.eq_one_iff _).mpr hw]
    exact Y.one_mem
  refine ⟨X, inferInstance, hWX, ?_, ?_⟩
  · calc
      X ≤ B.comap q := comap_mono hYB
      _ = H := comap_map_eq_self (by simpa only [q, QuotientGroup.ker_mk'] using hWH.le)
  · have hc : Nat.card (X.map q) = 2 := by
      rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective W)]; exact le_top)]
      simpa using hYc
    rwa [← relIndex_ker, QuotientGroup.ker_mk'] at hc

private theorem square_centralizes_step {P : Type*} [Group P]
    (W X K : Subgroup P) [W.Normal] [X.Normal] [IsElementaryAbelian 2 W]
    (hWX : W ≤ X) (hi : W.relIndex X = 2)
    (hK : K ≤ centralizer (W : Set P)) (k : K) :
    (k : P) ^ 2 ∈ centralizer (X : Set P) := by
  have hcomm : ⁅X, K⁆ ≤ W := commutator_le_of_normalized_index_two X W K hWX hi
    le_normalizer_of_normal le_normalizer_of_normal
  intro x hx
  let c : P := ⁅x, (k : P)⁆
  have hc : c ∈ W := hcomm (commutator_mem_commutator hx k.property)
  have hck : c * (k : P) = (k : P) * c := hK k.property c hc
  have hcc : c * c = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc
  have hconj : (k : P) * x * (k : P)⁻¹ = c⁻¹ * x := by
    dsimp [c]
    simp only [commutatorElement_def]
    group
  have hfix : (k : P) ^ 2 * x * ((k : P) ^ 2)⁻¹ = x := by
    calc
      (k : P) ^ 2 * x * ((k : P) ^ 2)⁻¹ =
          (k : P) * ((k : P) * x * (k : P)⁻¹) * (k : P)⁻¹ := by simp [pow_two, mul_assoc]
      _ = (k : P) * (c⁻¹ * x) * (k : P)⁻¹ := by rw [hconj]
      _ = c⁻¹ * ((k : P) * x * (k : P)⁻¹) := by
        rw [← mul_assoc, ← (Commute.inv_left hck).eq]
        group
      _ = c⁻¹ * (c⁻¹ * x) := by rw [hconj]
      _ = x := by rw [← mul_assoc, ← mul_inv_rev, hcc, inv_one, one_mul]
  exact (mul_inv_eq_iff_eq_mul.mp hfix).symm

/-- An involution in a centralizing cyclic-four section has a fixed point
outside a proper normal elementary two-subgroup. -/
public theorem fixed_not_le_of_centralizing_cyclic_four_section {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (W H : Subgroup P) [W.Normal] [H.Normal]
    [IsElementaryAbelian 2 W] (hWH : W < H)
    (K : Subgroup P) (Z : Subgroup K) [Z.Normal] [IsCyclic (K ⧸ Z)]
    (hquot : Nat.card (K ⧸ Z) = 4)
    (hZ : Z ≤ (center P).comap K.subtype)
    (hK : K ≤ centralizer (W : Set P))
    (t : K) (ht : t ^ 2 = 1) :
    ¬ H ⊓ centralizer ({(t : P)} : Set P) ≤ W := by
  intro hfixed
  obtain ⟨X, hXn, hWX, hXH, hi⟩ := normal_step P hP W H hWH
  let : X.Normal := hXn
  have htX : (t : P) ∈ centralizer (X : Set P) := by
    exact mem_of_square_eq_one_of_cyclic_four_quotient Z
      ((centralizer (X : Set P)).comap K.subtype) hquot
      (hZ.trans (comap_mono (center_le_centralizer _)))
      (square_centralizes_step W X K hWX hi hK) t ht
  have hXW : X ≤ W := by
    intro x hx
    exact hfixed ⟨hXH hx, mem_centralizer_singleton_iff.mpr (htX x hx)⟩
  have := relIndex_eq_one.mpr hXW
  omega

end Subgroup
