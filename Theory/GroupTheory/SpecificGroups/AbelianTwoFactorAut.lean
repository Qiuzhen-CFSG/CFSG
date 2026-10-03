module
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Automorphisms of an abelian two-group with unequal cyclic factors

For `n ≥ 2`, the automorphism group of `C_(2^n) × C_2` is a two-group.
The result is also transported along an actual group equivalence. This
supplies the abelian-factor automorphism restriction used in the centric
subgroup analysis of Alperin–Brauer–Gorenstein, Chapter II §1 Lemma 3,
article p.10, independently of any chosen wreathed presentation.

The square kernel `C` is a characteristic Klein four subgroup. The image
`D` of the `2^(n-1)`-power map is characteristic, has order two, and lies
in `C`; hence every automorphism fixes its unique nonidentity element.
The induced automorphism group on `C` is therefore a two-group by the
Klein four fixed-element theorem. The quotient by `C` is cyclic, because
the first cyclic factor maps onto it, so its automorphism group is also
a two-group. The kernel of the combined restriction and quotient action
is a two-group by the characteristic-subgroup automorphism kernel theorem.
Exact kernel and image cardinalities use the cyclic power-map formulas.
The hypothesis `n ≥ 2` ensures the second factor has trivial power image
and excludes the Klein four group, whose automorphism group has order six.
-/

namespace AbelianTwoFactorAut
private abbrev A (n : ℕ) := Multiplicative (ZMod (2 ^ n))
private abbrev B := Multiplicative (ZMod 2)
private abbrev G (n : ℕ) := A n × B
private def C (n : ℕ) : Subgroup (G n) := (powMonoidHom 2).ker
private def D (n : ℕ) : Subgroup (G n) := (powMonoidHom (2 ^ (n-1))).range

private theorem C_characteristic (n : ℕ) : (C n).Characteristic := by
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

private theorem D_characteristic (n : ℕ) : (D n).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro f
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨f z, (map_pow f z _).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(f.symm y) ^ (2^(n-1)), ⟨f.symm y, rfl⟩, by simp⟩

private theorem card_C (n : ℕ) (hn : 1 ≤ n) : Nat.card (C n) = 4 := by
  have he : C n = (powMonoidHom 2 : A n →* A n).ker.prod
      (powMonoidHom 2 : B →* B).ker := by
    ext x
    change x ^ 2 = 1 ↔ x.1 ^ 2 = 1 ∧ x.2 ^ 2 = 1
    exact Prod.ext_iff
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker]
  have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  simp [A, B, Nat.gcd_eq_right hd]

private theorem card_D (n : ℕ) (hn : 2 ≤ n) : Nat.card (D n) = 2 := by
  have he : D n = (powMonoidHom (2^(n-1)) : A n →* A n).range.prod
      (powMonoidHom (2^(n-1)) : B →* B).range := by
    rw [← MonoidHom.range_prodMap]
    rfl
  rw [he, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_range]
  have hd : 2 ^ (n-1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
  have h2d : 2 ∣ 2 ^ (n-1) := dvd_pow_self 2 (by omega)
  simp only [A, B, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, Nat.gcd_eq_right hd,
    Nat.gcd_eq_left h2d, Nat.div_self (by decide : 0 < 2), mul_one]
  have he : 2 ^ n = 2 ^ (n-1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [he]
  exact Nat.mul_div_right 2 (by positivity)

private theorem D_le_C (n : ℕ) (hn : 1 ≤ n) : D n ≤ C n := by
  rintro x ⟨y, rfl⟩
  change (y ^ (2^(n-1))) ^ 2 = 1
  have he : 2 ^ (n-1) * 2 = 2 ^ n := by rw [← pow_succ]; congr 1; omega
  rw [← pow_mul, he]
  apply Prod.ext
  · change (y.1) ^ (2^n) = 1
    simpa [A] using (pow_card_eq_one' (x := y.1))
  · change (y.2) ^ (2^n) = 1
    have hy : (y.2)^2 = 1 := by simpa [B] using (pow_card_eq_one' (x := y.2))
    obtain ⟨k,hk⟩ := dvd_pow_self 2 (by omega : n ≠ 0)
    rw [hk, pow_mul, hy, one_pow]

private theorem B_sq (b : B) : b ^ 2 = 1 := by simpa [B] using (pow_card_eq_one' (x := b))

private theorem quotient_cyclic (n : ℕ) : IsCyclic (G n ⧸ C n) := by
  let : (C n).Normal := Subgroup.normal_of_isMulCommutative _
  let f : A n →* G n ⧸ C n := (QuotientGroup.mk' (C n)).comp (MonoidHom.inl (A n) B)
  apply isCyclic_of_surjective f
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    refine ⟨x.1, ?_⟩
    change QuotientGroup.mk' (C n) (x.1, 1) = QuotientGroup.mk' (C n) x
    apply QuotientGroup.eq.mpr
    change ((x.1, (1 : B))⁻¹ * x) ^ 2 = 1
    apply Prod.ext
    · simp
    · simpa using B_sq x.2
private theorem C_klein (n : ℕ) (hn : 1 ≤ n) : IsKleinFour (C n) := by
  let : Nontrivial (C n) := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_C n hn]; decide)
  refine ⟨card_C n hn, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  apply orderOf_eq_prime _ hx
  exact Subtype.ext x.property

private theorem fixed_involution (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : C n, c ≠ 1 ∧ ∀ f : MulAut (G n), f c = (c : G n) := by
  let : (D n).Characteristic := D_characteristic n
  obtain ⟨d, hd, huniq⟩ := (Nat.card_eq_two_iff' (1 : D n)).mp (card_D n hn)
  let c : C n := ⟨d, D_le_C n (by omega) d.property⟩
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hd
    have he : (d : G n) = 1 := congrArg (fun x : C n => (x : G n)) hc
    exact Subtype.ext he
  · intro f
    have hf : MulAut.characteristic (D n) f d ≠ 1 := by
      intro he
      apply hd
      exact (MulAut.characteristic (D n) f).injective (he.trans (map_one _).symm)
    have he := huniq (MulAut.characteristic (D n) f d) hf
    exact congrArg Subtype.val he
private theorem model_result (n : ℕ) (hn : 2 ≤ n) : IsPGroup 2 (MulAut (G n)) := by
  let : (C n).Characteristic := C_characteristic n
  let : IsKleinFour (C n) := C_klein n (by omega)
  let : IsCyclic (G n ⧸ C n) := quotient_cyclic n
  have hG : IsPGroup 2 (G n) := IsPGroup.of_card (show Nat.card (G n) = 2 ^ (n+1) by
    simp [G, A, B, pow_succ])
  apply Subgroup.isPGroup_mulAut_of_characteristic_action_ranges (C n) (hG.to_subgroup _)
  · obtain ⟨c, hc, hfix⟩ := fixed_involution n hn
    apply IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one
      (MulAut.characteristic (C n)).range hc
    rintro f ⟨a, rfl⟩
    exact Subtype.ext (hfix a)
  · exact ((hG.to_quotient (C n)).mulAut_of_isCyclic_two).to_subgroup _
end AbelianTwoFactorAut

/-- Unequal cyclic factors of orders `2^n` and `2`, for `n ≥ 2`, have a two-group of automorphisms. -/
public theorem abelian_two_factor_aut_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (MulAut (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) :=
  AbelianTwoFactorAut.model_result n hn

/-- Transport the automorphism restriction along an actual product-model equivalence. -/
public theorem abelian_two_factor_aut_isPGroup_of_equiv
    {H : Type*} [Group H] {n : ℕ} (hn : 2 ≤ n)
    (e : H ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) :
    IsPGroup 2 (MulAut H) :=
  (abelian_two_factor_aut_isPGroup n hn).of_equiv (MulAut.congr e).symm
