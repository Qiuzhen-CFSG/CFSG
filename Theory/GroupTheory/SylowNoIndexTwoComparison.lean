module
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.NilpotentNoPrimeIndex

/-!
# Comparing normal Sylow intersections

Suppose K and L are normal subgroups of a finite group, K has two-power
index, and neither K nor L has a normal subgroup of index two. If the
commutator subgroup lies in ZL for a central subgroup Z, then every Sylow
two-subgroup meets K and L in the same subgroup.

The no-index-two condition on L kills its image in the two-group G/K,
giving L ≤ K. The commutator bound makes G/L nilpotent of class at most
two. Its subgroup image of K still has no normal subgroup of index two,
and therefore has odd order. The image of the two-group S ∩ K is thus
trivial, giving the reverse containment. We also expose the containment
and odd-relative-index steps for the actual source consumer.

This is the Sylow comparison in Alperin–Brauer–Gorenstein, Chapter II,
Section 3, Proposition 3 (article pp.25–26). No campaign predicates or
matrix-group classification results are required.
-/

namespace Subgroup
universe u

private theorem quotient_nilpotent_of_commutator_le_central_sup
    {G : Type u} [Group G] (Z L : Subgroup G) [L.Normal]
    (hZ : Z ≤ center G) (hc : _root_.commutator G ≤ Z ⊔ L) :
    Group.IsNilpotent (G ⧸ L) := by
  let q := QuotientGroup.mk' L
  have hZq : Z.map q ≤ center (G ⧸ L) := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L x
    simpa only [map_mul] using congrArg q ((mem_center_iff.mp (hZ hz)) g)
  have hcq : _root_.commutator (G ⧸ L) ≤ center (G ⧸ L) := by
    have hm := Subgroup.map_mono (f := q) hc
    rw [map_sup, show L.map q = ⊥ from (map_eq_bot_iff _).mpr (by simp [q]), sup_bot_eq] at hm
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective L)] at hm
    exact hm.trans hZq
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨2, Subgroup.lowerCentralSeries_succ_eq_bot ⊤ ?_⟩
  simpa only [top_lowerCentralSeries_one] using hcq

/-- The image of K in the central-by-abelian quotient has odd order. -/
public theorem odd_relIndex_of_no_normal_index_two_of_central_abelian_quotient
    {G : Type u} [Group G] [Finite G] (K L Z : Subgroup G) [L.Normal]
    (hK : ∀ M : Subgroup K, M.Normal → M.index ≠ 2)
    (hZ : Z ≤ center G) (hc : _root_.commutator G ≤ Z ⊔ L) :
    Odd (L.relIndex K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' L
  let I := K.map q
  let : Group.IsNilpotent (G ⧸ L) := quotient_nilpotent_of_commutator_le_central_sup Z L hZ hc
  let f : K →* I := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hno : ∀ M : Subgroup I, M.Normal → M.index ≠ 2 := by
    intro M hMN he
    let : M.Normal := hMN
    exact hK (M.comap f) inferInstance ((M.index_comap_of_surjective hf).trans he)
  have hi : ¬ 2 ∣ Nat.card I := Group.not_dvd_card_of_nilpotent_of_no_normal_index_prime hno
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd, ← QuotientGroup.ker_mk' L, relIndex_ker]
  exact hi

/-- A subgroup without normal index two lies in every normal subgroup
of two-power index. -/
public theorem le_of_no_normal_index_two_of_index_two_pow
    {G : Type u} [Group G] [Finite G] (L K : Subgroup G) [K.Normal]
    (n : ℕ) (hindex : K.index = 2 ^ n)
    (hL : ∀ M : Subgroup L, M.Normal → M.index ≠ 2) : L ≤ K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_normal_of_no_normal_index_prime L K hL
    (IsPGroup.of_card (by simpa only [← index_eq_card] using hindex))

/-- The two normal subgroups have identical intersections with each
chosen Sylow two-subgroup. -/
public theorem sylow_intersections_eq_of_central_abelian_quotient
    {G : Type u} [Group G] [Finite G] (K L Z : Subgroup G) [K.Normal] [L.Normal]
    (n : ℕ) (hindex : K.index = 2 ^ n)
    (hK : ∀ M : Subgroup K, M.Normal → M.index ≠ 2)
    (hL : ∀ M : Subgroup L, M.Normal → M.index ≠ 2)
    (hZ : Z ≤ center G) (hc : _root_.commutator G ≤ Z ⊔ L)
    (S : Sylow 2 G) : (S : Subgroup G) ⊓ K = (S : Subgroup G) ⊓ L := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK := le_of_no_normal_index_two_of_index_two_pow L K n hindex hL
  apply le_antisymm ?_ (inf_le_inf_left _ hLK)
  let q := QuotientGroup.mk' L
  let P := ((S : Subgroup G) ⊓ K).map q
  have hP : IsPGroup 2 P := (S.isPGroup'.to_inf_left (K := K)).map q
  have hPi : P ≤ K.map q := map_mono inf_le_right
  have hi : ¬ 2 ∣ Nat.card (K.map q) := by
    have ho := odd_relIndex_of_no_normal_index_two_of_central_abelian_quotient
      K L Z hK hZ hc
    rw [← QuotientGroup.ker_mk' L, relIndex_ker] at ho
    exact fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
  have hPbot : P = ⊥ := by
    rcases hP.card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · exact False.elim (hi (h.trans (card_dvd_of_le hPi)))
  intro x hx
  refine ⟨hx.1, (QuotientGroup.eq_one_iff (N := L) (x := x)).mp ?_⟩
  have hxP : q x ∈ P := mem_map_of_mem q hx
  simpa only [hPbot, mem_bot, q, QuotientGroup.mk'_apply] using hxP

end Subgroup

