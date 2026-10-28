module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Tactic.Group

/-!
# A dihedral rotation acting on a four-group

The two Weyl reflections act on the three nonidentity elements of a
four-group as transpositions, so their rotation centralizes it after the
sixth power. Once that power is involutory, both reflections centralize it
as well. These identities isolate the final kernel calculation for the
ternary G₂ completion, independently of any group presentation.

Source context: Aschbacher–Smith F.4.26, printed p.288.
-/

@[expose] public section

namespace Group
variable {G : Type*} [Group G]

/-- A three-cycle on a four-group centralizes it after the sixth power. -/
theorem sixth_commutes_of_torus_action (s t a b : G)
    (hs : s^2=1) (ht : t^2=1) (hb : b^2=1)
    (hab : Commute a b)
    (hsa : s*a*s=b) (hsb : s*b*s=a) (hta : t*a*t=a*b) (htb : t*b*t=b) :
    Commute ((t*s)^6) a ∧ Commute ((t*s)^6) b := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  let f := MulAut.conj (t*s)
  have hfa : f a=b := by
    change t*s*a*(t*s)⁻¹=b
    calc
      _ = t*(s*a*s)*t := by simp only [mul_inv_rev,hsi,hti]; group
      _ = b := by rw [hsa,htb]
  have hfb : f b=a*b := by
    change t*s*b*(t*s)⁻¹=a*b
    calc
      _ = t*(s*b*s)*t := by simp only [mul_inv_rev,hsi,hti]; group
      _ = a*b := by rw [hsb,hta]
  have hfab : f (a*b)=a := by
    rw [map_mul,hfa,hfb,←mul_assoc,←hab.eq,mul_assoc,←pow_two,hb,mul_one]
  have hc (z : G) (hz : z=a ∨ z=b) : Commute ((t*s)^3) z := by
    have hh : (f^3) z=z := by
      rcases hz with rfl | rfl <;>
        simp only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply,hfa,hfb,hfab]
    have he : (t*s)^3*z*((t*s)^3)⁻¹=z := by
      change MulAut.conj ((t*s)^3) z=z
      rw [map_pow]
      exact hh
    exact mul_inv_eq_iff_eq_mul.mp he
  constructor
  · simpa only [←pow_mul] using (hc a (Or.inl rfl)).pow_left 2
  · simpa only [←pow_mul] using (hc b (Or.inr rfl)).pow_left 2

/-- A reflection centralizes an involutory power of its dihedral rotation. -/
theorem reflections_commute_sixth (s t : G) (hs : s^2=1) (ht : t^2=1)
    (hq : ((t*s)^6)^2=1) : Commute s ((t*s)^6) ∧ Commute t ((t*s)^6) := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  have hqi : ((t*s)^6)⁻¹=(t*s)^6 := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hq)
  have hc (u : G) (hu : u=s ∨ u=t) : Commute u ((t*s)^6) := by
    have he : u*(t*s)*u⁻¹=(t*s)⁻¹ := by
      rcases hu with hu | hu
      · subst u
        simp only [mul_inv_rev,hsi,hti,mul_assoc,←pow_two,hs,mul_one]
      · subst u
        simp only [mul_inv_rev,hsi,hti,←mul_assoc,←pow_two,ht,one_mul]
    have hh : u*(t*s)^6*u⁻¹=(t*s)^6 := by rw [←conj_pow,he,inv_pow,hqi]
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact ⟨hc s (Or.inl rfl),hc t (Or.inr rfl)⟩
end Group
