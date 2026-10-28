module

public import Theory.FieldTheory.CyclotomicGalois

/-!
# Matching automorphisms on coprime roots of unity

For coprime positive orders `n` and `m`, every complex automorphism can be
matched on the `n`-th roots by an automorphism fixing all `m`-th roots.
Choose the exponent on a primitive root and lift its unit residue by CRT.
The cyclotomic automorphism for this lifted exponent has both required actions.

Source: the cyclotomic argument in Lyons, *A Characterization of the Group
U₃(4)* (1972), pp. 385–386.
-/

noncomputable section
open scoped Cyclotomic

private theorem unit_val_modEq {a b : ℕ} (hn : a * b ≠ 0)
    (w : (ZMod (a * b))ˣ) (u : (ZMod a)ˣ)
    (h : ZMod.unitsMap (Nat.dvd_mul_right a b) w = u) :
    (w : ZMod (a * b)).val ≡ (u : ZMod a).val [MOD a] := by
  have : NeZero (a * b) := ⟨hn⟩
  have : NeZero a := ⟨fun h => hn (by simp [h])⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [ZMod.natCast_zmod_val]
  have hv := ZMod.natCast_zmod_val (w : ZMod (a * b))
  have hc := congrArg (fun z : ZMod (a * b) => (z.cast : ZMod a)) hv
  rw [ZMod.cast_natCast (Nat.dvd_mul_right a b)] at hc
  rw [hc]
  exact congrArg Units.val h

/-- Match a complex automorphism on one order of roots while fixing a
coprime order of roots. -/
public theorem Section1.complex_galois_aut_match_roots {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hcop : n.Coprime m)
    (σ : ℂ ≃+* ℂ) :
    ∃ τ : Gal(ℂ/ℚ), (∀ z : ℂ, z ^ n = 1 → τ z = σ z) ∧
      (∀ z : ℂ, z ^ m = 1 → τ z = z) := by
  let : NeZero n := ⟨hn⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  have hσζ : IsPrimitiveRoot (σ ζ) n := hζ.map_of_injective σ.injective
  obtain ⟨e, _, he, heq⟩ := hζ.isPrimitiveRoot_iff.mp hσζ
  have hσ (z : ℂ) (hz : z ^ n = 1) : σ z = z ^ e := by
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, ← heq, ← pow_mul, ← pow_mul, Nat.mul_comm e i]
  obtain ⟨w, hwn, hwm⟩ := Section1.zmod_units_crt_exists_of_coprime hcop
    (ZMod.unitOfCoprime e he)
  let k := (w : ZMod (n * m)).val
  obtain ⟨τ, hτ⟩ := Section1.complex_galois_aut_pow_on_roots
    (ZMod.val_coe_unit_coprime w)
  have hkn : k ≡ e [MOD n] := by
    have h := unit_val_modEq (Nat.mul_ne_zero hn hm) w _ hwn
    apply h.trans
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact ZMod.coe_unitOfCoprime e he
  have hkm : k ≡ 1 [MOD m] := by
    exact Int.natCast_modEq_iff.mp
      (Section1.zmod_units_crt_val_modEq_right_one (Nat.mul_ne_zero hn hm) hwm)
  refine ⟨τ, ?_, ?_⟩
  · intro z hz
    rw [hτ z (by rw [pow_mul, hz, one_pow]), hσ z hz]
    exact pow_eq_pow_of_modEq hkn hz
  · intro z hz
    rw [hτ z (by rw [Nat.mul_comm n m, pow_mul, hz, one_pow])]
    exact (pow_eq_pow_of_modEq hkm hz).trans (pow_one z)
