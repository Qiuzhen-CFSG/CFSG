module
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.Index

/-!
# Normal subgroups at two successive indices of two

Let K be a normal subgroup of index two in a finite group G. If G has no
normal subgroup of index four, then K has no normal subgroup of index two.
This general index lemma supplies the additional assertion about K in the
Q and D alternatives of Alperin–Brauer–Gorenstein, Chapter II, Section 1,
Proposition 1 (article pp.10–11 of `refs/latex/alperin-brauer-gorenstein.tex`).

Suppose L has index two in K and view it as the actual image H in G.
Every square in G lies in K, so every fourth power lies in H. Conjugation
preserves fourth powers, hence they also lie in the normal core N of H.
The quotient G/N is consequently a finite two-group. Its order is divisible
by H's index four. The normal-subgroup existence theorem for finite p-groups
provides a normal subgroup of index four in G/N; pulling it back contradicts
the hypothesis. The proof uses only the given subgroup and its subtype image,
and the normal core is an internal construction.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- If the ambient group has no normal subgroup of index four, a normal
subgroup of index two has no further normal subgroup of index two. -/
public theorem no_normal_index_two_of_index_two_of_no_normal_index_four
    (K : Subgroup G) [K.Normal] (hK : K.index = 2)
    (hno4 : ∀ M : Subgroup G, M.Normal → M.index ≠ 4) :
    ∀ L : Subgroup K, L.Normal → L.index ≠ 2 := by
  intro L _hL hLindex
  let H := L.map K.subtype
  have hHi : H.index = 4 := by
    rw [show H = L.map K.subtype from rfl, index_map_subtype, hLindex, hK]
  have hpow (x : G) : x ^ 4 ∈ H := by
    let y : K := ⟨x ^ 2, K.sq_mem_of_index_two hK x⟩
    have hy : y ^ 2 ∈ L := L.sq_mem_of_index_two hLindex y
    have hh := Subgroup.mem_map_of_mem K.subtype hy
    change (x ^ 2) ^ 2 ∈ H at hh
    simpa only [← pow_mul] using hh
  let N := H.normalCore
  have hNpow (x : G) : x ^ 4 ∈ N := by
    intro g
    change (MulAut.conj g) (x ^ 4) ∈ H
    rw [map_pow]
    exact hpow _
  let Q := G ⧸ N
  have hQ : IsPGroup 2 Q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    refine ⟨2, ?_⟩
    change (QuotientGroup.mk' N g) ^ 4 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) (g ^ 4)).mpr (hNpow g)
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hn2 : 2 ≤ n := by
    have hd : 4 ∣ 2 ^ n := by
      rw [← hn, ← N.index_eq_card, ← hHi]
      exact index_dvd_of_le H.normalCore_le
    have hle := Nat.le_of_dvd (by positivity : 0 < 2 ^ n) hd
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hh : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hnle
    omega
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  obtain ⟨T, hT, _, hTc⟩ := exists_normal_subgroup_card_pow_of_normal
    (G := Q) (p := 2) (⊤ : Subgroup Q) inferInstance
    (by simpa only [Subgroup.card_top] using hn) (n - 2) (by omega)
  have hTi : T.index = 4 := by
    have hh := T.card_mul_index
    rw [hTc, hn] at hh
    have he : 2 ^ n = 2 ^ (n - 2) * 4 := by
      calc
        2 ^ n = 2 ^ ((n - 2) + 2) := by congr 1; omega
        _ = 2 ^ (n - 2) * 4 := by rw [pow_add]; rfl
    rw [he] at hh
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hh
  let : T.Normal := hT
  exact hno4 (T.comap (QuotientGroup.mk' N)) inferInstance
    ((T.index_comap_of_surjective (QuotientGroup.mk'_surjective N)).trans hTi)
end Subgroup
