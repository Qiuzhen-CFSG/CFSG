module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic

/-!
# Fourth powers of pointed dihedral automorphisms

An automorphism of D₁₀ acts on its rotation subgroup through the four
nonzero exponents modulo five. Its fourth power therefore fixes every
rotation. If the automorphism also fixes one nonidentity involution, that
reflection and the rotations generate D₁₀, so the fourth power is trivial.
The only finite certificate checks 100 generator-image pairs.

The DGS Chapter 8 path application uses this to retain the dihedral local
model in its Borel image theorem. Source: DGS, *Groups and Graphs* (1985),
8.5, printed p.139, the action of the two-edge path stabilizer.
-/

public section
namespace DihedralGroup
private def ev (x y : DihedralGroup 5) : DihedralGroup 5 → DihedralGroup 5
  | .r i => x ^ i.val
  | .sr i => y * x ^ i.val
private theorem heval (e : MulAut (DihedralGroup 5)) (z : DihedralGroup 5) :
    e z = ev (e (.r 1)) (e (.sr 0)) z := by
  cases z with
  | r i =>
    change e (.r i) = e (.r 1) ^ i.val
    rw [←map_pow,DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
  | sr i =>
    change e (.sr i) = e (.sr 0) * e (.r 1) ^ i.val
    rw [←map_pow,←map_mul,DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
    simp
/-- Fixing one nonidentity involution makes the fourth power of a D₁₀ automorphism trivial. -/
theorem fourth_pow_eq_one_of_fixed_involution (e : MulAut (DihedralGroup 5)) (s : DihedralGroup 5)
    (hs : s ^ 2 = 1) (hs1 : s ≠ 1) (he : e s = s) : e ^ 4 = 1 := by
  have cert : ∀ x y : DihedralGroup 5,
      x ^ 5 = 1 → x ≠ 1 →
      ev x y (ev x y (ev x y x)) = .r 1 := by decide +kernel
  have hr := cert (e (.r 1)) (e (.sr 0))
    (by rw [←map_pow,DihedralGroup.r_one_pow_n,map_one])
    (e.map_ne_one_iff.mpr (by decide))
  have h4 (z : DihedralGroup 5) : (e ^ 4) z = e (e (e (e z))) := by rfl
  have hrot : (e ^ 4) (.r 1) = .r 1 := by
    rw [h4,heval e (e (e (e (.r 1)))),heval e (e (e (.r 1))),heval e (e (.r 1))]
    exact hr
  have hrall (i : ZMod 5) : (e ^ 4) (.r i) = .r i := by
    have hh : (DihedralGroup.r i : DihedralGroup 5) = (.r 1) ^ i.val := by
      rw [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
    rw [hh,map_pow,hrot]
  have hs4 : (e ^ 4) s = s := by rw [h4,he,he,he,he]
  cases s with
  | r i =>
    have hi : (DihedralGroup.r i : DihedralGroup 5) = 1 :=
      (show ∀ i : ZMod 5, (DihedralGroup.r i : DihedralGroup 5)^2 = 1 → (DihedralGroup.r i : DihedralGroup 5) = 1 by decide +kernel) i hs
    exact (hs1 hi).elim
  | sr j =>
    apply MulEquiv.ext
    intro z
    cases z with
    | r i => exact hrall i
    | sr i =>
      have hh : (DihedralGroup.sr i : DihedralGroup 5) = .sr j * .r (i-j) := by simp
      change (e ^ 4) (.sr i) = .sr i
      rw [hh,map_mul,hs4,hrall]

end DihedralGroup
