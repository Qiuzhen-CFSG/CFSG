module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.ElementaryAbelian.Basic

/-!
# The central fourth-root kernel for a cyclic two-group times C₂

An automorphism subgroup fixing all involutions of `C_(2^n) × C₂` has
order at most four when its central automorphisms fixing fourth roots are
trivial. In fact elementary abelianness of the subgroup is unnecessary.

Choose a generator `x` of the long factor and a generator `z` of its
fourth-power kernel. Record the short coordinate of `f(x, 1)` and the
long-coordinate displacement of `f(z, 1)`. These define a homomorphism into
the product of two groups of order two. In its kernel, an automorphism is
an odd power map on the whole group, hence central, and fixes every fourth
root. The central-kernel hypothesis therefore makes the homomorphism
injective. This works uniformly, including the boundary case `n = 2`.

The elementary generator calculations follow
`AbelianCyclicTwoFixedAut.lean`. Source context: MacWilliams,
*Trans. AMS* 150 (1970), §1.2; Janko–Thompson (1970), Theorem 1.1, p.385.
-/

namespace AbelianCyclicTwoCentralKernelCount
private abbrev A (n : ℕ) := Multiplicative (ZMod (2 ^ n))
private abbrev B := Multiplicative (ZMod 2)
private abbrev G (n : ℕ) := A n × B

private theorem B_sq (b : B) : b ^ 2 = 1 := by
  simpa [B] using pow_card_eq_one' (x := b)

private theorem B_odd (b : B) {a : ℕ} (ha : Odd a) : b ^ a = b := by
  obtain ⟨k, rfl⟩ := ha
  rw [pow_add, pow_mul, B_sq, one_pow, one_mul, pow_one]

private theorem exists_power {C : Type*} [Group C] [Finite C] {x : C}
    (hx : ∀ y, y ∈ Subgroup.zpowers x) (y : C) : ∃ a : ℕ, x ^ a = y := by
  exact mem_powers_iff_mem_zpowers.mpr (hx y)

private theorem fixes_B {n : ℕ} (f : MulAut (G n))
    (hf : ∀ z, z ^ 2 = 1 → f z = z) (b : B) : f (1, b) = (1, b) := by
  apply hf
  exact Prod.ext (by simp) (B_sq b)

private theorem odd_coordinate {n : ℕ} (hn : 1 ≤ n) (x : A n)
    (hx : ∀ y, y ∈ Subgroup.zpowers x) (f : MulAut (G n))
    (hf : ∀ z, z ^ 2 = 1 → f z = z)
    {a : ℕ} {b : B} (hcoord : f (x, 1) = (x ^ a, b)) : Odd a := by
  let t := 2 ^ (n - 1)
  have ht : t * 2 = 2 ^ n := by dsimp [t]; rw [← pow_succ]; congr 1; omega
  have hxord : orderOf x = 2 ^ n := by
    simpa [A] using orderOf_eq_card_of_forall_mem_zpowers hx
  have hu2 : (x ^ t) ^ 2 = 1 := by
    rw [← pow_mul, ht]
    simpa only [hxord] using pow_orderOf_eq_one x
  have hu : x ^ t ≠ 1 := pow_ne_one_of_lt_orderOf (by dsimp [t]; positivity) (by
    rw [hxord, ← ht]
    have : 0 < t := by dsimp [t]; positivity
    omega)
  have he : (x ^ a) ^ t = x ^ t := by
    have h := hf ((x, (1 : B)) ^ t) (Prod.ext hu2 (by simp))
    rw [map_pow, hcoord] at h
    exact congrArg Prod.fst h
  rcases Nat.even_or_odd a with ha | ha
  · obtain ⟨k, hk⟩ := ha
    exfalso
    apply hu
    rw [← he, hk, show k + k = 2 * k by omega]
    rw [← pow_mul, show 2 * k * t = t * 2 * k by ring, pow_mul, pow_mul, hu2, one_pow]
  · exact ha

private theorem eval_pair {n : ℕ} (f : MulAut (G n))
    (hf : ∀ z, z ^ 2 = 1 → f z = z) (u : A n) (v : B) :
    f (u, v) = f (u, 1) * (1, v) := by
  rw [← fixes_B f hf v, ← map_mul]
  congr 1
  simp

private theorem scalar_of_short_eq_one {n : ℕ} (hn : 1 ≤ n) (x : A n)
    (hx : ∀ y, y ∈ Subgroup.zpowers x) (f : MulAut (G n))
    (hf : ∀ z, z ^ 2 = 1 → f z = z) (hb : (f (x, 1)).2 = 1) :
    ∃ a : ℕ, ∀ d, f d = d ^ a := by
  obtain ⟨a, ha⟩ := exists_power hx (f (x, 1)).1
  have hcoord : f (x, 1) = (x ^ a, 1) := Prod.ext ha.symm hb
  have hoa := odd_coordinate hn x hx f hf hcoord
  refine ⟨a, ?_⟩
  rintro ⟨u, v⟩
  obtain ⟨k, rfl⟩ := exists_power hx u
  rw [eval_pair f hf]
  have he : (x ^ k, (1 : B)) = (x, (1 : B)) ^ k := by simp
  rw [he, map_pow, hcoord]
  apply Prod.ext
  · simp [← pow_mul, Nat.mul_comm]
  · simpa using (B_odd v hoa).symm

private theorem short_comp {n : ℕ} (hn : 1 ≤ n) (x : A n)
    (hx : ∀ y, y ∈ Subgroup.zpowers x) (f g : MulAut (G n))
    (hf : ∀ z, z ^ 2 = 1 → f z = z)
    (hg : ∀ z, z ^ 2 = 1 → g z = z) :
    (f (g (x, 1))).2 = (f (x, 1)).2 * (g (x, 1)).2 := by
  obtain ⟨a, ha⟩ := exists_power hx (g (x, 1)).1
  have hcoord : g (x, 1) = (x ^ a, (g (x, 1)).2) := Prod.ext ha.symm rfl
  have hoa := odd_coordinate hn x hx g hg hcoord
  conv_lhs => rw [hcoord, eval_pair f hf]
  have he : (x ^ a, (1 : B)) = (x, (1 : B)) ^ a := by simp
  rw [he, map_pow]
  simpa using congrArg (fun b : B => b * (g (x, 1)).2) (B_odd (f (x, 1)).2 hoa)

private theorem displacement_sq {n : ℕ} (z : A n) (hz : z ^ 4 = 1)
    (f : MulAut (G n)) (hf : ∀ d, d ^ 2 = 1 → f d = d) :
    ((f (z, 1)).1 * z⁻¹) ^ 2 = 1 := by
  have he : (f (z, 1)).1 ^ 2 = z ^ 2 := by
    have hh := hf ((z, (1 : B)) ^ 2) (by
      apply Prod.ext
      · change (z ^ 2) ^ 2 = 1
        simpa only [← pow_mul] using hz
      · simp)
    rw [map_pow] at hh
    exact congrArg Prod.fst hh
  rw [mul_pow, inv_pow, he, mul_inv_cancel]

private theorem displacement_comp {n : ℕ} (z : A n) (hz : z ^ 4 = 1)
    (f g : MulAut (G n)) (hf : ∀ d, d ^ 2 = 1 → f d = d)
    (hg : ∀ d, d ^ 2 = 1 → g d = d) :
    (f (g (z, 1))).1 * z⁻¹ =
      ((f (z, 1)).1 * z⁻¹) * ((g (z, 1)).1 * z⁻¹) := by
  let d := (g (z, 1)).1 * z⁻¹
  have hd : f (d, 1) = (d, 1) := hf _ (Prod.ext (displacement_sq z hz g hg) (by simp))
  have he : g (z, 1) = (d, 1) * (z, 1) * (1, (g (z, 1)).2) := by
    apply Prod.ext <;> simp [d]
  conv_lhs => rw [he, map_mul, map_mul, hd, fixes_B f hf]
  simp only [Prod.fst_mul, mul_one]
  dsimp [d]
  ac_rfl

private theorem count {K : Type*} [Group K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (ρ : K →* MulAut (G n))
    (hfix : ∀ k : K, ∀ d, d ^ 2 = 1 → ρ k d = d)
    (hkill : ∀ k : K, (∃ a : ℕ, ∀ d, ρ k d = d ^ a) →
      (∀ d, d ^ 4 = 1 → ρ k d = d) → k = 1) : Nat.card K ≤ 4 := by
  let C := (powMonoidHom 4 : A n →* A n).ker
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := A n)
  obtain ⟨z, hzgen⟩ := IsCyclic.exists_generator (α := C)
  have hz : (z : A n) ^ 4 = 1 := z.property
  let j : K →* ((powMonoidHom 2 : A n →* A n).ker × B) :=
    { toFun := fun k =>
        (⟨(ρ k ((z : A n), 1)).1 * (z : A n)⁻¹,
          displacement_sq (z : A n) hz (ρ k) (hfix k)⟩,
          (ρ k (x, 1)).2)
      map_one' := by
        apply Prod.ext
        · apply Subtype.ext
          simp
        · simp
      map_mul' := by
        intro k l
        apply Prod.ext
        · apply Subtype.ext
          simpa only [map_mul, MulAut.mul_apply, Prod.fst_mul, Subgroup.coe_mul] using
            displacement_comp (z : A n) hz (ρ k) (ρ l) (hfix k) (hfix l)
        · simpa only [map_mul, MulAut.mul_apply, Prod.snd_mul] using
            short_comp hn x hx (ρ k) (ρ l) (hfix k) (hfix l) }
  have hj : Function.Injective j := by
    apply j.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro k hk
    change k = 1
    have he : j k = 1 := hk
    have hlong : (ρ k ((z : A n), 1)).1 * (z : A n)⁻¹ = 1 :=
      congrArg (fun v : (powMonoidHom 2 : A n →* A n).ker × B => (v.1 : A n)) he
    have hshort : (ρ k (x, 1)).2 = 1 := congrArg Prod.snd he
    obtain ⟨a, ha⟩ := scalar_of_short_eq_one hn x hx (ρ k) (hfix k) hshort
    apply hkill k ⟨a, ha⟩
    have hfixz : ρ k ((z : A n), 1) = ((z : A n), 1) := by
      apply Prod.ext
      · exact mul_inv_eq_one.mp hlong
      · rw [ha]
        simp
    rintro ⟨u, v⟩ hd
    have hu : u ∈ C := congrArg Prod.fst hd
    obtain ⟨b, hb⟩ := exists_power hzgen (⟨u, hu⟩ : C)
    have hub : u = (z : A n) ^ b := (congrArg (fun w : C => (w : A n)) hb).symm
    rw [hub, eval_pair (ρ k) (hfix k)]
    have hp : ((z : A n) ^ b, (1 : B)) = ((z : A n), (1 : B)) ^ b := by simp
    rw [hp, map_pow, hfixz]
    simp
  have hcard : Nat.card ((powMonoidHom 2 : A n →* A n).ker × B) = 4 := by
    rw [Nat.card_prod, IsCyclic.card_powMonoidHom_ker]
    have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    simp [A, B, Nat.gcd_eq_right hd]
  exact (Nat.card_le_card_of_injective j hj).trans_eq hcard

end AbelianCyclicTwoCentralKernelCount

/-- A subgroup of automorphisms of a cyclic two-group times `C₂` fixing the
involutions has order at most four if its central fourth-root kernel is trivial. -/
public theorem abelian_cyclic_two_aut_card_le_four_of_central_kernel
    {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    {n : ℕ} (hn : 2 ≤ n)
    (e : H ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)))
    (A : Subgroup (MulAut H))
    (hfix : ∀ f ∈ A, ∀ d : H, d ^ 2 = 1 → f d = d)
    (hcentral : ∀ f ∈ A, f ∈ Subgroup.center (MulAut H) →
      (∀ d : H, d ^ 4 = 1 → f d = d) → f = 1) : Nat.card A ≤ 4 := by
  let ρ := (MulAut.congr e).toMonoidHom.comp A.subtype
  apply AbelianCyclicTwoCentralKernelCount.count (by omega : 1 ≤ n) ρ
  · intro f d hd
    change e (f.val (e.symm d)) = d
    rw [hfix f.val f.property (e.symm d) (by rw [← map_pow, hd, map_one]),
      e.apply_symm_apply]
  · intro f hscalar hfour
    obtain ⟨a, ha⟩ := hscalar
    have hpow (d : H) : f.val d = d ^ a := by
      apply e.injective
      simpa [ρ] using ha (e d)
    apply Subtype.ext
    apply hcentral f.val f.property
    · apply Subgroup.mem_center_iff.mpr
      intro g
      apply MulEquiv.ext
      intro d
      change g (f.val d) = f.val (g d)
      rw [hpow, hpow, map_pow]
    · intro d hd
      apply e.injective
      have he : (e d) ^ 4 = 1 := by rw [← map_pow, hd, map_one]
      simpa [ρ] using hfour (e d) he


/-- The elementary abelian specialization of the central fourth-root kernel
count, in the form used for elementary automorphism actions. -/
public theorem abelian_cyclic_two_elementary_aut_card_le_four_of_central_kernel
    {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    {n : ℕ} (hn : 2 ≤ n)
    (e : H ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)))
    (A : Subgroup (MulAut H)) [IsElementaryAbelian 2 A]
    (hfix : ∀ f ∈ A, ∀ d : H, d ^ 2 = 1 → f d = d)
    (hcentral : ∀ f ∈ A, f ∈ Subgroup.center (MulAut H) →
      (∀ d : H, d ^ 4 = 1 → f d = d) → f = 1) : Nat.card A ≤ 4 :=
  abelian_cyclic_two_aut_card_le_four_of_central_kernel hn e A hfix hcentral
