module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Displacement into an involution's fixed space

In characteristic two, let b be an involution and let r commute with b.
If r fixes C_V(b) pointwise, then every displacement r(v)-v lies in C_V(b).
Indeed b(v)-v is fixed by b, and applying r to that displacement gives the
required equality. No dimension or faithfulness hypothesis is needed.

Source application: Aschbacher--Smith, 15.2.28, printed p.1119, where the
Sylow action is cyclic and the distinguished plane is C_V(b).
-/

public section

namespace Representation
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem neg_binary (v : W) : -v = v := by
  have h : v + v = 0 := by
    have hh := zero_smul (ZMod 2) v
    rw [show (0 : ZMod 2) = 1 + 1 by decide, add_smul, one_smul] at hh
    exact hh
  exact neg_eq_iff_add_eq_zero.mpr h

/-- An actor commuting with an involution and fixing its fixed space has
all its displacements in that same fixed space. -/
theorem displacement_fixed_of_commute_and_fixes
    (ρ : Representation (ZMod 2) D W) {b r : D} (hb : b ^ 2 = 1)
    (hc : Commute b r) (hf : ∀ w, ρ b w = w → ρ r w = w) (v : W) :
    ρ b (ρ r v - v) = ρ r v - v := by
  have hbb (w : W) : ρ b (ρ b w) = w := by
    rw [←Module.End.mul_apply,←map_mul,←pow_two,hb,map_one]
    rfl
  have hbr (w : W) : ρ b (ρ r w) = ρ r (ρ b w) := by
    rw [←Module.End.mul_apply,←map_mul,hc.eq,map_mul,Module.End.mul_apply]
  have hd : ρ r (ρ b v - v) = ρ b v - v := by
    apply hf
    rw [map_sub,hbb,sub_eq_add_neg,neg_binary,sub_eq_add_neg,neg_binary,add_comm]
  rw [map_sub] at hd
  rw [map_sub,hbr]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hd

end Representation
