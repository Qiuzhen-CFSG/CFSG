module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Simultaneous coordinates for Janko's eleven- and five-generators

A fixed-point-free permutation of order eleven and a permutation with two
fixed points satisfying `b * a * b⁻¹ = a^4` admit the displayed coordinates
for `ell` and `m`. Take the two fixed points as origins. The normalizer
relation shows that they lie in distinct eleven-orbits. Their powers give
an injective 22-point frame, hence a bijection. In that frame `a` adds one
and `b` multiplies by four, exactly as in the concrete Janko permutations.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 9, pp.17–18,
DOI 10.1016/0021-8693(68)90002-1. We use left composition and label 22 as 0.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
open JankoModel

private theorem eleven_orbit_injective (a : Equiv.Perm (Fin 22))
    (ha : orderOf a = 11) (hfree : ∀ x, a x ≠ x) (x : Fin 22) :
    Function.Injective (fun i : Fin 11 => (a ^ i.val) x) := by
  have hp : a ^ 11 = 1 := ha ▸ pow_orderOf_eq_one a
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hperiod : Function.minimalPeriod a x = 11 :=
    Function.minimalPeriod_eq_prime (by
      change (a ^ 11) x = x
      rw [hp, Equiv.Perm.one_apply]) (hfree x)
  intro i j hij
  apply Fin.ext
  apply Function.iterate_injOn_Iio_minimalPeriod (f := a) (x := x)
  · simpa only [Set.mem_Iio, hperiod] using i.isLt
  · simpa only [Set.mem_Iio, hperiod] using j.isLt
  · exact hij

private theorem eleven_pow_mod (a : Equiv.Perm (Fin 22))
    (ha : orderOf a = 11) (i : ℕ) : a ^ (i % 11) = a ^ i := by
  simpa only [ha] using pow_mod_orderOf a i

private theorem fixed_in_eleven_orbit (a b : Equiv.Perm (Fin 22))
    (ha : orderOf a = 11) (hfree : ∀ x, a x ≠ x)
    (hab : SemiconjBy b a (a ^ 4)) (x y : Fin 22)
    (hx : b x = x) (hy : b y = y) (k : ℕ) (hk : (a ^ k) x = y) : x = y := by
  let i : Fin 11 := ⟨k % 11, Nat.mod_lt _ (by decide)⟩
  have hi : (a ^ i.val) x = y := by
    dsimp [i]
    rw [eleven_pow_mod a ha, hk]
  have h4 : (a ^ (4 * i.val)) x = y := by
    have h := congrArg (fun p : Equiv.Perm (Fin 22) => p x) (hab.pow_right i.val).eq
    simpa only [Equiv.Perm.mul_apply, hi, hy, hx, ← pow_mul] using h.symm
  have hi4 : (⟨(4 * i.val) % 11, Nat.mod_lt _ (by decide)⟩ : Fin 11) = i := by
    apply eleven_orbit_injective a ha hfree x
    change (a ^ ((4 * i.val) % 11)) x = (a ^ i.val) x
    rw [eleven_pow_mod a ha, h4, hi]
  have hiv : (4 * i.val) % 11 = i.val := congrArg Fin.val hi4
  have hiz : i.val = 0 := by omega
  simpa only [hiz, pow_zero, Equiv.Perm.one_apply] using hi

private def elevenFrame (a : Equiv.Perm (Fin 22)) (x y : Fin 22)
    (z : Bool × Fin 11) : Fin 22 := (a ^ z.2.val) (if z.1 then x else y)

private theorem elevenFrame_injective (a b : Equiv.Perm (Fin 22))
    (ha : orderOf a = 11) (hfree : ∀ x, a x ≠ x)
    (hab : SemiconjBy b a (a ^ 4)) (x y : Fin 22)
    (hx : b x = x) (hy : b y = y) (hxy : x ≠ y) :
    Function.Injective (elevenFrame a x y) := by
  have hdisj (i j : Fin 11) : (a ^ i.val) x ≠ (a ^ j.val) y := by
    intro h
    have h' := congrArg (fun z => (a ^ (11 - j.val)) z) h
    have hperiod : a ^ 11 = 1 := ha ▸ pow_orderOf_eq_one a
    have hexp : 11 - j.val + j.val = 11 := by omega
    have hshift : (a ^ (11 - j.val + i.val)) x = y := by
      simpa only [← Equiv.Perm.mul_apply, ← pow_add, hexp, hperiod,
        Equiv.Perm.one_apply] using h'
    exact hxy (fixed_in_eleven_orbit a b ha hfree hab x y hx hy _ hshift)
  rintro ⟨c, i⟩ ⟨d, j⟩ hij
  cases c <;> cases d
  · have he := eleven_orbit_injective a ha hfree y hij
    exact Prod.ext rfl he
  · exact False.elim (hdisj j i hij.symm)
  · exact False.elim (hdisj i j hij)
  · have he := eleven_orbit_injective a ha hfree x hij
    exact Prod.ext rfl he

private theorem elevenFrame_a (a : Equiv.Perm (Fin 22)) (ha : orderOf a = 11)
    (x y : Fin 22) (c : Bool) (i : Fin 11) :
    a (elevenFrame a x y (c, i)) = elevenFrame a x y (c, i + 1) := by
  unfold elevenFrame
  change (a * a ^ i.val) (if c then x else y) =
    (a ^ ((i + 1 : Fin 11).val)) (if c then x else y)
  rw [← pow_succ', Fin.val_add]
  exact congrArg (fun p : Equiv.Perm (Fin 22) => p (if c then x else y))
    (eleven_pow_mod a ha (i.val + 1)).symm

private theorem elevenFrame_b (a b : Equiv.Perm (Fin 22)) (ha : orderOf a = 11)
    (hab : SemiconjBy b a (a ^ 4)) (x y : Fin 22)
    (hx : b x = x) (hy : b y = y) (c : Bool) (i : Fin 11) :
    b (elevenFrame a x y (c, i)) = elevenFrame a x y (c, 4 * i) := by
  have hb : b (if c then x else y) = (if c then x else y) := by
    cases c <;> assumption
  have h := congrArg (fun p : Equiv.Perm (Fin 22) => p (if c then x else y))
    (hab.pow_right i.val).eq
  unfold elevenFrame
  rw [Fin.val_mul, show (4 : Fin 11).val = 4 from rfl, eleven_pow_mod a ha]
  simpa only [Equiv.Perm.mul_apply, hb, ← pow_mul] using h

private def modelFrame : Bool × Fin 11 → Fin 22 := elevenFrame ell 11 0

set_option maxRecDepth 100000 in
private theorem modelFrame_bijective : Function.Bijective modelFrame := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem modelFrame_ell : ∀ c : Bool, ∀ i : Fin 11,
    ell (modelFrame (c, i)) = modelFrame (c, i + 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem modelFrame_m : ∀ c : Bool, ∀ i : Fin 11,
    m (modelFrame (c, i)) = modelFrame (c, 4 * i) := by
  decide +kernel

/-- Choose the two fixed points of the five-generator as origins of the
fixed-point-free eleven-generator's cycles. Both generators then have the
coordinates displayed by Janko. -/
public theorem exists_eleven_five_coordinates (a b : Equiv.Perm (Fin 22))
    (ha : orderOf a = 11) (hfree : ∀ x, a x ≠ x)
    (hbfix : (Finset.univ.filter (fun x => b x = x)).card = 2)
    (hab : b * a * b⁻¹ = a ^ 4) :
    ∃ p : Equiv.Perm (Fin 22), (MulAut.conj p) a = ell ∧ (MulAut.conj p) b = m := by
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hbfix
  have hx : b x = x := by
    have hm : x ∈ Finset.univ.filter (fun x => b x = x) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  have hy : b y = y := by
    have hm : y ∈ Finset.univ.filter (fun x => b x = x) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  have hsemi : SemiconjBy b a (a ^ 4) := by
    change b * a = a ^ 4 * b
    rw [← hab, mul_assoc, inv_mul_cancel, mul_one]
  have hbij : Function.Bijective (elevenFrame a x y) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨elevenFrame_injective a b ha hfree hsemi x y hx hy hxy, by decide⟩
  let e : (Bool × Fin 11) ≃ Fin 22 := Equiv.ofBijective (elevenFrame a x y) hbij
  let t : (Bool × Fin 11) ≃ Fin 22 := Equiv.ofBijective modelFrame modelFrame_bijective
  let p : Equiv.Perm (Fin 22) := e.symm.trans t
  have hp (z : Bool × Fin 11) : p (elevenFrame a x y z) = modelFrame z := by
    change t (e.symm (e z)) = t z
    rw [e.symm_apply_apply]
  have hp_inv (z : Bool × Fin 11) : p⁻¹ (modelFrame z) = elevenFrame a x y z := by
    apply p.injective
    change (p * p⁻¹) (modelFrame z) = p (elevenFrame a x y z)
    rw [mul_inv_cancel, Equiv.Perm.one_apply, hp]
  refine ⟨p, ?_, ?_⟩
  · apply Equiv.ext
    intro w
    obtain ⟨⟨c, i⟩, rfl⟩ := modelFrame_bijective.2 w
    change p (a (p⁻¹ (modelFrame (c, i)))) = ell (modelFrame (c, i))
    rw [hp_inv, elevenFrame_a a ha, hp, modelFrame_ell]
  · apply Equiv.ext
    intro w
    obtain ⟨⟨c, i⟩, rfl⟩ := modelFrame_bijective.2 w
    change p (b (p⁻¹ (modelFrame (c, i)))) = m (modelFrame (c, i))
    rw [hp_inv, elevenFrame_b a b ha hsemi x y hx hy, hp, modelFrame_m]

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
