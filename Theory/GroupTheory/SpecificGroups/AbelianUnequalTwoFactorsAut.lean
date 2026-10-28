module

public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Automorphisms of two unequal cyclic two-group factors

The automorphism group of `C_(2^n) × C_(2^m)` is a two-group when `m < n`.
The highest nontrivial power image is characteristic of order two, so every
induced automorphism of the square kernel fixes its nonidentity element.
This kernel is Klein four when both factors are nontrivial. The square map
identifies the quotient with cyclic factors of exponents `n-1` and `m-1`;
induction and the characteristic-subgroup automorphism kernel theorem finish.

This generalizes the elementary unequal-factor argument needed in
Janko–Thompson, Math. Z. 113 (1970), §6, p.394.
-/

namespace AbelianUnequalTwoFactorsAut
private abbrev A (n : ℕ) := Multiplicative (ZMod (2 ^ n))
private abbrev G (n m : ℕ) := A n × A m
private def C (n m : ℕ) : Subgroup (G n m) := (powMonoidHom 2).ker
private def D (n m : ℕ) : Subgroup (G n m) := (powMonoidHom (2 ^ (n-1))).range

private theorem C_characteristic (n m : ℕ) : (C n m).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro f
  ext x
  change (f x) ^ 2 = 1 ↔ x ^ 2 = 1
  constructor
  · intro hx
    apply f.injective
    calc
      f (x ^ 2) = (f x) ^ 2 := map_pow f x 2
      _ = f 1 := hx.trans (map_one f).symm
  · intro hx
    rw [← map_pow, hx, map_one]

private theorem D_characteristic (n m : ℕ) : (D n m).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro f
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨f z, (map_pow f z _).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(f.symm y) ^ (2^(n-1)), ⟨f.symm y, rfl⟩, by simp⟩

private theorem card_C (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : Nat.card (C n m) = 4 := by
  have he : C n m = (powMonoidHom 2 : A n →* A n).ker.prod
      (powMonoidHom 2 : A m →* A m).ker := by
    ext x
    change x ^ 2 = 1 ↔ x.1 ^ 2 = 1 ∧ x.2 ^ 2 = 1
    exact Prod.ext_iff
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker]
  have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hmd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  simp [A, Nat.gcd_eq_right hd, Nat.gcd_eq_right hmd]

private theorem card_D (n m : ℕ) (hn : m < n) : Nat.card (D n m) = 2 := by
  have he : D n m = (powMonoidHom (2^(n-1)) : A n →* A n).range.prod
      (powMonoidHom (2^(n-1)) : A m →* A m).range := by
    rw [← MonoidHom.range_prodMap]
    rfl
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_range]
  have hd : 2 ^ (n-1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
  have h2d : 2 ^ m ∣ 2 ^ (n-1) := pow_dvd_pow 2 (by omega)
  simp only [A, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, Nat.gcd_eq_right hd,
    Nat.gcd_eq_left h2d, Nat.div_self (by positivity : 0 < 2 ^ m), mul_one]
  have he : 2 ^ n = 2 ^ (n-1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [he]
  exact Nat.mul_div_right 2 (by positivity)

private theorem D_le_C (n m : ℕ) (hn : m < n) : D n m ≤ C n m := by
  rintro x ⟨y, rfl⟩
  change (y ^ (2^(n-1))) ^ 2 = 1
  have he : 2 ^ (n-1) * 2 = 2 ^ n := by rw [← pow_succ]; congr 1; omega
  rw [← pow_mul, he]
  apply Prod.ext
  · change (y.1) ^ (2^n) = 1
    simpa [A] using (pow_card_eq_one' (x := y.1))
  · change (y.2) ^ (2^n) = 1
    have hy : (y.2)^(2^m) = 1 := by simpa [A] using (pow_card_eq_one' (x := y.2))
    obtain ⟨k,hk⟩ := pow_dvd_pow 2 (by omega : m ≤ n)
    rw [hk, pow_mul, hy, one_pow]

private theorem C_klein (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : IsKleinFour (C n m) := by
  let : Nontrivial (C n m) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [card_C n m hn hm]; decide)
  refine ⟨card_C n m hn hm, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  apply orderOf_eq_prime _ hx
  exact Subtype.ext x.property

private theorem fixed_involution (n m : ℕ) (hn : m < n) :
    ∃ c : C n m, c ≠ 1 ∧ ∀ f : MulAut (G n m), f c = (c : G n m) := by
  let : (D n m).Characteristic := D_characteristic n m
  obtain ⟨d, hd, huniq⟩ := (Nat.card_eq_two_iff' (1 : D n m)).mp (card_D n m hn)
  let c : C n m := ⟨d, D_le_C n m hn d.property⟩
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hd
    have he : (d : G n m) = 1 := congrArg (fun x : C n m => (x : G n m)) hc
    exact Subtype.ext he
  · intro f
    have hf : MulAut.characteristic (D n m) f d ≠ 1 := by
      intro he
      apply hd
      exact (MulAut.characteristic (D n m) f).injective (he.trans (map_one _).symm)
    have he := huniq (MulAut.characteristic (D n m) f d) hf
    exact congrArg Subtype.val he

private theorem card_square_range (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (powMonoidHom 2 : A n →* A n).range = 2 ^ (n-1) := by
  rw [IsCyclic.card_powMonoidHom_range]
  have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  simp only [A, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    Nat.gcd_eq_right hd]
  have he : 2 ^ n = 2 ^ (n-1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]

private noncomputable def squareRangeEquiv (n : ℕ) (hn : 1 ≤ n) :
    (powMonoidHom 2 : A n →* A n).range ≃* A (n-1) :=
  mulEquivOfCyclicCardEq (by rw [card_square_range n hn]; simp [A])

private noncomputable def quotientEquiv (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    G n m ⧸ C n m ≃* G (n-1) (m-1) := by
  have he : (powMonoidHom 2 : G n m →* G n m).range =
      (powMonoidHom 2 : A n →* A n).range.prod
        (powMonoidHom 2 : A m →* A m).range := by
    rw [← MonoidHom.range_prodMap]
    rfl
  exact (QuotientGroup.quotientKerEquivRange (powMonoidHom 2 : G n m →* G n m)).trans
    ((MulEquiv.subgroupCongr he).trans
      ((Subgroup.prodEquiv _ _).trans
        ((squareRangeEquiv n hn).prodCongr (squareRangeEquiv m hm))))

private theorem model_result (n m : ℕ) (hn : m < n) : IsPGroup 2 (MulAut (G n m)) := by
  induction m generalizing n with
  | zero =>
    let : Subsingleton (A 0) := (Nat.card_eq_one_iff_unique.mp (by simp [A])).1
    let : Unique (A 0) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    have he : G n 0 ≃* A n := MulEquiv.prodUnique
    have hA : IsPGroup 2 (A n) := IsPGroup.of_card (show Nat.card (A n) = 2^n by simp [A])
    exact hA.mulAut_of_isCyclic_two.of_equiv (MulAut.congr he).symm
  | succ m ih =>
    let : (C n (m+1)).Characteristic := C_characteristic n (m+1)
    let : IsKleinFour (C n (m+1)) := C_klein n (m+1) (by omega) (by omega)
    have hG : IsPGroup 2 (G n (m+1)) := IsPGroup.of_card
      (show Nat.card (G n (m+1)) = 2 ^ (n+(m+1)) by simp [G, A, pow_add])
    apply Subgroup.isPGroup_mulAut_of_characteristic_action_ranges (C n (m+1))
      (hG.to_subgroup _)
    · obtain ⟨c, hc, hfix⟩ := fixed_involution n (m+1) hn
      apply IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one
        (MulAut.characteristic (C n (m+1))).range hc
      rintro f ⟨a, rfl⟩
      exact Subtype.ext (hfix a)
    · have hq : IsPGroup 2 (MulAut (G n (m+1) ⧸ C n (m+1))) :=
        (ih (n-1) (by omega)).of_equiv
          (MulAut.congr (quotientEquiv n (m+1) (by omega) (by omega))).symm
      exact hq.to_subgroup _

end AbelianUnequalTwoFactorsAut

/-- Two unequal cyclic two-group factors have a two-group of automorphisms. -/
public theorem abelian_unequal_two_factors_aut_isPGroup (n m : ℕ) (h : n ≠ m) :
    IsPGroup 2 (MulAut (Multiplicative (ZMod (2 ^ n)) ×
      Multiplicative (ZMod (2 ^ m)))) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (AbelianUnequalTwoFactorsAut.model_result m n h).of_equiv
      (MulAut.congr MulEquiv.prodComm)
  · exact AbelianUnequalTwoFactorsAut.model_result n m h
