module

public import Theory.Character.LinearTwist
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# Odd automizers detected by prime-degree characters

An order-`p` Sylow subgroup with odd centralizer has odd automizer whenever a
complex degree-`p` representation vanishes on `p`-singular elements and takes
values `±3` on involutions.

If the automizer is even, Cauchy's theorem gives an involution in the
normalizer outside the centralizer. Its action on the prime-order subgroup
is fixed-point-free, hence inversion, giving an embedded dihedral group.
All reflections of this group have the same character value `c`. Averaging
the restricted representation and its sign twist gives the nonnegative
multiplicities `(1 + c) / 2` and `(1 - c) / 2`, incompatible with `c = ±3`.

Source: Alperin--Brauer--Gorenstein, III.8 Lemma 4, article p.116,
`refs/original/n-group-global/semidihedral-source/abg-iii7-8.txt`.
-/

open scoped BigOperators
open DihedralGroup

private def signCharacter (n : ℕ) : DihedralGroup n →* ℂ where
  toFun | .r _ => 1 | .sr _ => -1
  map_one' := rfl
  map_mul' := by rintro (i | i) (j | j) <;> simp

private theorem sum_dihedral {n : ℕ} [NeZero n] (f : DihedralGroup n → ℂ) :
    ∑ x, f x = (∑ i : ZMod n, f (.r i)) + ∑ i : ZMod n, f (.sr i) := by
  rw [← (DihedralGroup.equivSum.symm).sum_comp f, Fintype.sum_sum_type]
  rfl

private theorem reflection_value {n : ℕ} (hn : Odd n)
    (ρ : Representation ℂ (DihedralGroup n) (Fin n → ℂ)) (i : ZMod n) :
    ρ.character (.sr i) = ρ.character (.sr 0) := by
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  let j : ZMod n := -(↑u⁻¹ * i)
  have hj : -j - j = i := by
    dsimp [j]
    have hu : (2 : ZMod n) * (↑u⁻¹ * i) = i := u.mul_inv_cancel_left i
    linear_combination hu
  have h := ρ.char_conj (.sr 0) (.r j)
  simpa only [inv_r, r_mul_sr, sr_mul_r, zero_sub, ← sub_eq_add_neg, hj] using h

private theorem dihedral_contradiction {n : ℕ} (hn : Odd n)
    (ρ : Representation ℂ (DihedralGroup n) (Fin n → ℂ))
    (hzero : ∀ i : ZMod n, i ≠ 0 → ρ.character (.r i) = 0)
    (hvalue : ρ.character (.sr 0) = 3 ∨ ρ.character (.sr 0) = -3) : False := by
  classical
  let : NeZero n := ⟨hn.pos.ne'⟩
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.pos.ne'
  let : Invertible (Nat.card (DihedralGroup n) : ℂ) := invertibleOfNonzero
    (by simpa only [DihedralGroup.nat_card, Nat.cast_mul, Nat.cast_ofNat]
      using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hnC)
  let τ := ρ.linearTwist (signCharacter n)
  let a := Module.finrank ℂ ρ.invariants
  let b := Module.finrank ℂ τ.invariants
  have ha := ρ.card_inv_mul_sum_char_eq_finrank
  have hb := τ.card_inv_mul_sum_char_eq_finrank
  have hrot : ∑ i : ZMod n, ρ.character (.r i) = (n : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      exact hzero i hi
    · simp
  have hsum : ∑ x, ρ.character x = n + n * ρ.character (.sr 0) := by
    rw [sum_dihedral, hrot]
    simp only [reflection_value hn ρ, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
  have hsumSign : ∑ x, τ.character x = n - n * ρ.character (.sr 0) := by
    rw [sum_dihedral]
    simp only [τ, Representation.linearTwist_character]
    change (∑ i : ZMod n, (1 : ℂ) * ρ.character (.r i)) +
      (∑ i : ZMod n, (-1 : ℂ) * ρ.character (.sr i)) = _
    simp only [one_mul, neg_mul, reflection_value hn ρ,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hrot]
    ring
  have ha' : n + n * ρ.character (.sr 0) = (2 * n : ℂ) * a := by
    rw [hsum] at ha
    simp only [DihedralGroup.nat_card, Nat.cast_mul, Nat.cast_ofNat] at ha
    exact (inv_mul_eq_iff_eq_mul₀ (mul_ne_zero (by norm_num) hnC)).mp ha
  have hb' : n - n * ρ.character (.sr 0) = (2 * n : ℂ) * b := by
    rw [hsumSign] at hb
    simp only [DihedralGroup.nat_card, Nat.cast_mul, Nat.cast_ofNat] at hb
    exact (inv_mul_eq_iff_eq_mul₀ (mul_ne_zero (by norm_num) hnC)).mp hb
  rcases hvalue with hv | hv
  · rw [hv] at hb'
    have hh := congrArg Complex.re hb'
    simp at hh
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith
  · rw [hv] at ha'
    have hh := congrArg Complex.re ha'
    simp at hh
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith

private theorem embedding_dihedral {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (P : Subgroup G) (hP : Nat.card P = p)
    (hC : Odd (Nat.card (Subgroup.centralizer (P : Set G))))
    (hN : ¬ Odd (Nat.card (Subgroup.normalizer (P : Set G)))) :
    ∃ f : DihedralGroup p →* G, Function.Injective f := by
  let N := Subgroup.normalizer (P : Set G)
  let C := Subgroup.centralizer (P : Set G)
  have htdiv : 2 ∣ Nat.card N := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hN)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 htdiv
  have htG : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have htC : (t : G) ∉ C := by
    intro hc
    apply hC.not_two_dvd_nat
    rw [← htG]
    exact Subgroup.orderOf_dvd_natCard C hc
  have htP : (t : G) ∉ P := by
    intro htP
    apply hp.not_two_dvd_nat
    rw [← hP, ← htG]
    exact Subgroup.orderOf_dvd_natCard P htP
  let φ : MulAut P := P.normalizerMonoidHom t
  have hφne : φ ≠ 1 := by
    intro he
    apply htC
    have htker : t ∈ P.normalizerMonoidHom.ker := he
    rwa [P.normalizerMonoidHom_ker] at htker
  have hfree : MonoidHom.FixedPointFree φ := by
    intro x hx
    by_contra hxne
    apply hφne
    ext y
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp
      (mem_zpowers_of_prime_card hP hxne : y ∈ Subgroup.zpowers x)
    rw [← hk, map_zpow, hx]
    rfl
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hφ2 : φ ^ 2 = 1 := by
    change P.normalizerMonoidHom t ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hinvol : Function.Involutive φ := by
    intro x
    exact congrArg (fun f : MulAut P => f x) hφ2
  have hinv (r : G) (hr : r ∈ P) : (t : G) * r * (t : G)⁻¹ = r⁻¹ := by
    exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨r, hr⟩)
  have htG2 : (t : G) ^ 2 = 1 := by rw [← htG]; exact pow_orderOf_eq_one _
  obtain ⟨e⟩ := P.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted (t : G)
    (isCyclic_of_prime_card hP) htG2 htP hinv
  rw [hP] at e
  let f : DihedralGroup p →* G := (P ⊔ Subgroup.zpowers (t : G)).subtype.comp e.symm.toMonoidHom
  exact ⟨f, Subtype.val_injective.comp e.symm.injective⟩

/-- If a degree-`p` representation vanishes on `p`-singular elements and takes
values `±3` on involutions, an order-`p` Sylow subgroup with odd centralizer has
odd automizer. -/
public theorem Representation.odd_automizer_of_prime_degree {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (P : Sylow p G) (hP : Nat.card P = p)
    (hC : Odd (Nat.card (Subgroup.centralizer (P : Set G))))
    (ρ : Representation ℂ G (Fin p → ℂ))
    (hzero : ∀ g : G, p ∣ orderOf g → ρ.character g = 0)
    (hvalue : ∀ t : G, orderOf t = 2 → ρ.character t = 3 ∨ ρ.character t = -3) :
    Odd ((Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G))) := by
  have hN : Odd (Nat.card (Subgroup.normalizer (P : Set G))) := by
    by_contra hN
    obtain ⟨f, hf⟩ := embedding_dihedral hp (P : Subgroup G) hP hC hN
    apply dihedral_contradiction hp (ρ.comp f)
    · intro i hi
      change ρ.character (f (.r i)) = 0
      apply hzero
      have horder : orderOf (DihedralGroup.r i) = p := by
        apply orderOf_eq_prime
        · simp
        · simpa only [← DihedralGroup.r_zero, ne_eq, DihedralGroup.r.injEq] using hi
      rw [orderOf_injective f hf, horder]
    · change ρ.character (f (.sr 0)) = 3 ∨ ρ.character (f (.sr 0)) = -3
      apply hvalue
      rw [orderOf_injective f hf, DihedralGroup.orderOf_sr]
  exact hN.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
