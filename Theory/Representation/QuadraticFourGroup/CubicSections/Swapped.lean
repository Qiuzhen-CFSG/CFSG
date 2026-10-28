module

public import Theory.Representation.QuadraticFourGroup.CubicSections.Dihedral

/-!
# The swapped cubic generators in Step 4

Let an involution `a` interchange two commuting groups. If `x` is cubic in
the first group and an involution `b` inverts it there, set `y = xᵃ` and
`c = aᵇ`. Then `a` inverts `x⁻¹y`, while `c` inverts `xy` and centralizes
`x⁻¹y`. The cubic dihedral calculation transfers fixed vectors from `x` to
`y` when `c` fixes displacements by `a`.

This verifies the group calculation in GLS, volume 2, Theorem 25.14,
Step 4, using the corrected first rotation `x⁻¹xᵃ`. The transcription
`x⁻¹aˣ` is not that rotation. The proof uses the inverse of the second
rotation so that their product is exactly `x`.
-/

@[expose] public section

namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem conj_twice {a z : G} (ha : a * a = 1) :
    a * (a * z * a⁻¹) * a⁻¹ = z := by
  calc _ = (a * a) * z * (a * a)⁻¹ := by group
       _ = z := by rw [ha]; simp

private theorem inv_inv_mul_of_cube {x : G} (hx : x ^ 3 = 1) : x⁻¹ * x⁻¹ = x := by
  have hx' : x * x = x⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa [pow_succ, pow_two] using hx)
  calc _ = (x * x)⁻¹ := (mul_inv_rev x x).symm
       _ = x := by rw [hx', inv_inv]

/-- The corrected Step 4 rotations are `x⁻¹ * xᵃ` and `x * xᵃ`.
A quadratic identity for `a` and `aᵇ` transfers fixed vectors from `x` to `xᵃ`. -/
theorem swapped_cubic_fixed_imp (ρ : Representation (ZMod 2) G V)
    {a b x : G} (ha : a * a = 1) (hb : b * b = 1) (hx : x ^ 3 = 1)
    (hbx : b * x * b⁻¹ = x⁻¹)
    (hxy : Commute x (a * x * a⁻¹)) (hby : Commute b (a * x * a⁻¹))
    (hquad : ∀ v, ρ (b * a * b⁻¹) (ρ a v - v) = ρ a v - v) :
    ∀ v, ρ x v = v → ρ (a * x * a⁻¹) v = v := by
  let y := a * x * a⁻¹
  let c := b * a * b⁻¹
  let r := x⁻¹ * y
  let s := x⁻¹ * y⁻¹
  have hxy' : Commute x y := hxy
  have hby' : Commute b y := hby
  have hax : MulAut.conj a x = y := rfl
  have hay : MulAut.conj a y = x := conj_twice ha
  have hcconj (z : G) : c * z * c⁻¹ = b * (a * (b * z * b⁻¹) * a⁻¹) * b⁻¹ := by
    have h0 : c * z * c⁻¹ = b * (a * (b⁻¹ * z * b) * a⁻¹) * b⁻¹ := by
      dsimp [c]; group
    rw [h0]
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    simp only [hb']
  have hy : y ^ 3 = 1 := by
    change (MulAut.conj a x) ^ 3 = 1
    rw [← map_pow, hx, map_one]
  have hc : c * c = 1 := by
    change (MulAut.conj b a) * (MulAut.conj b a) = 1
    rw [← map_mul, ha, map_one]
  have hcx : c * x * c⁻¹ = y⁻¹ := by
    rw [hcconj, hbx]
    change b * (MulAut.conj a x⁻¹) * b⁻¹ = y⁻¹
    rw [map_inv, hax]
    exact hby'.inv_right.mul_inv_cancel
  have hcy : c * y * c⁻¹ = x⁻¹ := by
    rw [hcconj, hby'.mul_inv_cancel]
    change b * (MulAut.conj a y) * b⁻¹ = x⁻¹
    rw [hay, hbx]
  have hr : r ^ 3 = 1 := by
    rw [show r = x⁻¹ * y from rfl, hxy.inv_left.mul_pow, inv_pow, hx, hy]
    simp
  have hs : s ^ 3 = 1 := by
    rw [show s = x⁻¹ * y⁻¹ from rfl, hxy.inv_inv.mul_pow, inv_pow, inv_pow, hx, hy]
    simp
  have har : a * r * a⁻¹ = r⁻¹ := by
    change MulAut.conj a (x⁻¹ * y) = (x⁻¹ * y)⁻¹
    rw [map_mul, map_inv, hax, hay]
    simpa only [inv_inv] using (mul_inv_rev x⁻¹ y).symm
  have hcs : c * s * c⁻¹ = s⁻¹ := by
    change MulAut.conj c (x⁻¹ * y⁻¹) = (x⁻¹ * y⁻¹)⁻¹
    rw [map_mul, map_inv, map_inv]
    change (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ = _
    rw [hcx, hcy, inv_inv, inv_inv]
    simpa only [inv_inv] using (mul_inv_rev x⁻¹ y⁻¹).symm
  have hrc : Commute r c := by
    have hr' : c * r * c⁻¹ = r := by
      change MulAut.conj c (x⁻¹ * y) = x⁻¹ * y
      rw [map_mul, map_inv]
      change (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹) = _
      rw [hcx, hcy, inv_inv, hxy'.inv_left.eq]
    exact (mul_inv_eq_iff_eq_mul.mp hr').symm
  have hrs : Commute r s :=
    ((Commute.refl x⁻¹).mul_left hxy'.inv_left.symm).mul_right
      ((hxy'.inv_left.mul_left (Commute.refl y)).inv_right)
  have hrsx : r * s = x := by
    dsimp [r, s]
    rw [hxy'.inv_left.symm.mul_mul_mul_comm, mul_inv_cancel, mul_one]
    exact inv_inv_mul_of_cube hx
  have hrsy : r⁻¹ * s = y := by
    dsimp [r, s]
    rw [mul_inv_rev, inv_inv]
    calc y⁻¹ * x * (x⁻¹ * y⁻¹) = y⁻¹ * y⁻¹ := by group
         _ = y := inv_inv_mul_of_cube hy
  intro v hv
  have hfix := (dihedral_cubic_fixed_iff ρ ha hc hr hs har hcs hrc hrs hquad v).mp
    (hrsx.symm ▸ hv)
  have hir : ρ r⁻¹ v = v := by
    calc _ = ρ r⁻¹ (ρ r v) := by rw [hfix.1]
         _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  change ρ y v = v
  rw [← hrsy, map_mul, Module.End.mul_apply, hfix.2, hir]

end Representation.QuadraticFourGroup

end
