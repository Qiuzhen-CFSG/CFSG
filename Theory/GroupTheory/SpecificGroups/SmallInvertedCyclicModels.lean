module
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.QuaternionPresentation
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Small groups with an inverted cyclic subgroup of index two

A finite group whose order divides eight and which has a cyclic subgroup of
index two inverted by every outside element is cyclic, a Klein four-group,
dihedral of order eight, or quaternion of order eight. The divisibility
hypothesis excludes groups of order six, which also have an inverted cyclic
subgroup of index two.

For order four, a noncyclic group has every nonidentity element of order two.
For order eight, choose a generator `c` of the cyclic subgroup and an outside
element `d`. The two cosets establish generation by `c` and `d`. Inversion
forces `d²` to be a self-inverse element of the cyclic subgroup of order four,
so `d²` is either `1` or `c²`. The dihedral and quaternion presentation
recognizers then identify the group.

This is the elementary small-subgroup recognition used in the fusion analysis
following Alperin–Brauer–Gorenstein, Chapter II, Section 1, Lemma 1 (article
p. 9). It is independent of the ambient quasi-dihedral group; the ABG adapter
supplies the index, order divisibility, and inversion hypotheses.
-/

private theorem cyclic_or_klein_four {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 4) : IsCyclic G ∨ IsKleinFour G := by
  classical
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  right
  have hnt : Nontrivial G := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  let := hnt
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro g hg
  have hd : orderOf g ∣ 4 := hcard ▸ orderOf_dvd_natCard g
  have hn : orderOf g ≠ 1 := by simpa using hg
  have h4 : orderOf g ≠ 4 := fun h => hcyc (isCyclic_of_orderOf_eq_card g (h.trans hcard.symm))
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf g ∣ 2 ^ 2 from hd)
  interval_cases k
  · exact (hn he).elim
  · exact he
  · exact (h4 he).elim

private theorem order_eight_models {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : IsCyclic A) (hi : A.index = 2)
    (hcard : Nat.card G = 8)
    (hinv : ∀ x : G, x ∉ A → ∀ t : G, t ∈ A → x * t * x⁻¹ = t⁻¹) :
    Nonempty (G ≃* DihedralGroup 4) ∨ Nonempty (G ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨c, hcA⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp hA
  have hcMem : c ∈ A := hcA ▸ Subgroup.mem_zpowers c
  have hc : orderOf c = 4 := by
    have h := A.index_mul_card
    rw [hi, hcard] at h
    have hcAcard : Nat.card A = 4 := by omega
    rw [← hcA, Nat.card_zpowers] at hcAcard
    exact hcAcard
  obtain ⟨d, hdA, hdcoset⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hi
  let B := Subgroup.closure ({c, d} : Set G)
  have hcB : c ∈ B := Subgroup.subset_closure (by simp)
  have hdB : d ∈ B := Subgroup.subset_closure (by simp)
  have hAB : A ≤ B := by rw [← hcA]; exact Subgroup.zpowers_le.mpr hcB
  have hgen : B = ⊤ := by
    apply top_unique
    intro x _
    rcases hdcoset x with hx | hx
    · have h := B.mul_mem (B.inv_mem hdB) (hAB hx)
      simpa only [inv_mul_cancel_left] using h
    · exact hAB hx
  have hdc : d * c * d⁻¹ = c⁻¹ := hinv d hdA c hcMem
  have hsqA : d ^ 2 ∈ A := Subgroup.sq_mem_of_index_two hi d
  have hsqinv : d ^ 2 = (d ^ 2)⁻¹ := by
    calc
      d ^ 2 = d * d ^ 2 * d⁻¹ := by group
      _ = (d ^ 2)⁻¹ := hinv d hdA (d ^ 2) hsqA
  have hfour : (d ^ 2) ^ 2 = 1 := by
    rw [pow_two]
    calc
      d ^ 2 * d ^ 2 = d ^ 2 * (d ^ 2)⁻¹ := congrArg (d ^ 2 * ·) hsqinv
      _ = 1 := mul_inv_cancel _
  have hsqcases : d ^ 2 = 1 ∨ d ^ 2 = c ^ 2 := by
    rw [← hcA, mem_zpowers_iff_mem_range_orderOf] at hsqA
    rcases Finset.mem_image.mp hsqA with ⟨k, hk, heq⟩
    have hk4 : k < 4 := by simpa [hc] using hk
    interval_cases k
    · exact Or.inl (by simpa using heq.symm)
    · exfalso
      rw [← heq] at hfour
      have hpow : c ^ 2 = 1 := by simpa only [pow_one] using hfour
      have := orderOf_dvd_of_pow_eq_one hpow
      norm_num [hc] at this
    · exact Or.inr heq.symm
    · exfalso
      rw [← heq] at hfour
      have hpow : c ^ 6 = 1 := by simpa only [← pow_mul] using hfour
      have := orderOf_dvd_of_pow_eq_one hpow
      norm_num [hc] at this
  rcases hsqcases with hs | hs
  · exact Or.inl (dihedralGroup_equiv_of_presentation (by decide) c d hc hs hdc hgen hcard)
  · exact Or.inr (QuaternionGroup.quaternionGroup_equiv_of_presentation
      (by decide) c d hc hs hdc hgen hcard)

/-- A group of order dividing eight with an inverted cyclic subgroup of index two
is cyclic, Klein four, dihedral of order eight, or quaternion of order eight. -/
public theorem small_inverted_cyclic_models {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : IsCyclic A) (hi : A.index = 2)
    (hcard : Nat.card G ∣ 8)
    (hinv : ∀ x : G, x ∉ A → ∀ t : G, t ∈ A → x * t * x⁻¹ = t⁻¹) :
    IsCyclic G ∨ IsKleinFour G ∨ Nonempty (G ≃* DihedralGroup 4) ∨
      Nonempty (G ≃* QuaternionGroup 2) := by
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card G ∣ 2 ^ 3 from hcard)
  interval_cases k
  · have h1 : Nat.card G = 1 := he
    let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Or.inl inferInstance
  · exact Or.inl (isCyclic_of_prime_card (p := 2) he)
  · rcases cyclic_or_klein_four he with hc | hk
    · exact Or.inl hc
    · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr (order_eight_models A hA hi he hinv))
