module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic

/-!
# Root parameters for a quadratic field involution

For a field of order 25 and a nonidentity involution σ, choose a nonzero
trace-zero element a with a² + 1 ≠ 0. Scaling a by 2 when necessary gives
this choice, since the characteristic is five. Put z = 1 + a. The square of z / σ(z) is not fixed
by σ: otherwise expanding the fourth powers of 1 ± a gives 8a(a² + 1) = 0.

Consequently a - σ(a) and (z / σ(z))²(a - σ(a)) are independent over the
prime field. Counting their 25 linear combinations proves that they additively
span the whole field. These are the two root parameters used by the four
field-involution conjugates in the matrix calculation.

Source: the field-automorphism generation bound in Guralnick--Malle,
Classification of 2F-modules I, Proposition 4.1, manuscript pp.8--9;
Aschbacher--Smith K.2, printed p.453. The calculation supplies the generation
assertion used there without any representation-theoretic hypothesis.
-/

public section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F]

/-- A root displacement and its torus conjugate additively span the field. -/
theorem exists_root_span_parameters_twentyFive (hcard : Nat.card F = 25)
    (σ : F ≃+* F) (hs : σ ^ 2 = 1) (hne : σ ≠ 1) :
    ∃ a z : F, z ≠ 0 ∧
      ∀ x : F, ∃ n m : ℕ,
        x = n • (a - σ a) + m • ((z / σ z) ^ 2 * (a - σ a)) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hcard)
  have h2 : (2 : F) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < 5))
      ((CharP.cast_eq_zero_iff F 5 2).mp h)
  have h3 : (3 : F) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (by omega : 3 < 5))
      ((CharP.cast_eq_zero_iff F 5 3).mp h)
  have hs' (x : F) : σ (σ x) = x := by
    simpa [pow_two] using DFunLike.congr_fun hs x
  obtain ⟨b, hb⟩ : ∃ b : F, σ b ≠ b := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  let d := b - σ b
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hsd : σ d = -d := by simp [d, hs']
  obtain ⟨a, ha, hsa, ha2⟩ : ∃ a : F, a ≠ 0 ∧ σ a = -a ∧ a ^ 2 + 1 ≠ 0 := by
    by_cases h : d ^ 2 + 1 = 0
    · refine ⟨2 * d, mul_ne_zero h2 hd, by rw [map_mul, map_ofNat, hsd]; ring, ?_⟩
      intro hh
      apply h3
      linear_combination 4 * h - hh
    · exact ⟨d, hd, hsd, h⟩
  have ha1 : 1 + a ≠ 0 := by
    intro h
    have hh := congrArg σ h
    simp only [map_add, map_one, map_zero, hsa] at hh
    apply h2
    linear_combination h + hh
  have hma1 : 1 - a ≠ 0 := by
    have := σ.injective.ne ha1
    simpa only [map_add, map_one, map_zero, hsa, sub_eq_add_neg] using this
  let z := 1 + a
  let w := z / σ z
  have hw : w = (1 + a) / (1 - a) := by simp [w, z, hsa, sub_eq_add_neg]
  have hsw : σ w = (1 - a) / (1 + a) := by simp [w, z, hsa, sub_eq_add_neg]
  have hw2 : σ (w ^ 2) ≠ w ^ 2 := by
    rw [map_pow, hsw, hw]
    intro he
    have he' : (1 - a) ^ 4 = (1 + a) ^ 4 := by
      have := (div_eq_div_iff (pow_ne_zero 2 ha1) (pow_ne_zero 2 hma1)).mp
        (show (1 - a) ^ 2 / (1 + a) ^ 2 = (1 + a) ^ 2 / (1 - a) ^ 2 by
          simpa only [div_pow] using he)
      convert this using 1 <;> ring
    have hz : (2 : F) ^ 3 * a * (a ^ 2 + 1) = 0 := by
      linear_combination -he'
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h2) ha) ha2) hz
  let f : ZMod 5 →+* F := ZMod.castHom (dvd_refl 5) F
  have hfσ (c : ZMod 5) : σ (f c) = f c := by
    have h := RingHom.ext_zmod (σ.toRingHom.comp f) f
    exact DFunLike.congr_fun h c
  let v := a - σ a
  have hv : v ≠ 0 := by
    simpa only [v, hsa, sub_neg_eq_add, ← two_mul] using mul_ne_zero h2 ha
  let L : ZMod 5 × ZMod 5 → F := fun c => f c.1 * v + f c.2 * (w ^ 2 * v)
  have hLi : Function.Injective L := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ he
    have he' : f (c - c') + f (d - d') * w ^ 2 = 0 := by
      apply (mul_eq_zero.mp (show
        (f (c - c') + f (d - d') * w ^ 2) * v = 0 by
          dsimp [L] at he
          simp only [map_sub]
          linear_combination he)).resolve_right hv
    have heσ := congrArg σ he'
    simp only [map_add, map_mul, hfσ, map_zero] at heσ
    have hdz : f (d - d') = 0 := by
      have hz : f (d - d') * (σ (w ^ 2) - w ^ 2) = 0 := by
        linear_combination heσ - he'
      exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hw2)
    have hcz : f (c - c') = 0 := by simpa [hdz] using he'
    exact Prod.ext (sub_eq_zero.mp (f.injective (hcz.trans (map_zero f).symm)))
      (sub_eq_zero.mp (f.injective (hdz.trans (map_zero f).symm)))
  have hLs : Function.Surjective L := (hLi.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_prod]
    simp [Nat.card_eq_fintype_card])).2
  refine ⟨a, z, ha1, ?_⟩
  intro x
  obtain ⟨⟨c, d⟩, hc⟩ := hLs x
  refine ⟨c.val, d.val, ?_⟩
  simpa only [L, f, v, w, nsmul_eq_mul, ZMod.castHom_apply, ZMod.cast_eq_val] using hc.symm
end FiniteField
