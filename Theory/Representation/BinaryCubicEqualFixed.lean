module

public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# Equal fixed spaces force a normalized cubic to act trivially

Let an involution commute with a cubic operator and let another operator
invert that cubic. If every vector fixed by the involution is also fixed
by the inverter, the cubic is the identity. The proof uses actual linear
operators and works on the entire module without a splitting premise.

Source application: Aschbacher--Smith12.7.19, printed p.846.
-/

public section
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_neg (v : V) : -v = v := by
  have he : v + v = 0 := by
    calc
      v+v = ((1:ZMod 2)+1) • v := by rw [add_smul,one_smul]
      _ = 0 := by rw [show (1:ZMod 2)+1=0 by decide,zero_smul]
  exact neg_eq_of_add_eq_zero_left he

/-- Actual fixed-space containment, a commuting involution and an
inverter exclude every nontrivial cubic action. -/
theorem cubic_eq_one_of_fixed_containment
    (c t s : BinaryLinear.GL V) (hc : c^3=1) (ht : t*t=1)
    (htc : Commute t c) (hsc : s*c=c^2*s)
    (hfix : ∀ v : V, t v=v → s v=v) : c=1 := by
  have hfixed (v : V) (hv : t v=v) : c v=v := by
    have htv : t (c v)=c v := by
      have hh := congrArg (fun g : BinaryLinear.GL V => g v) htc.eq
      change t (c v)=c (t v) at hh
      rwa [hv] at hh
    have he := congrArg (fun g : BinaryLinear.GL V => g v) hsc
    change s (c v)=(c^2) (s v) at he
    rw [hfix (c v) htv,hfix v hv] at he
    have hh : c v=c (c v) := by simpa only [pow_two,LinearEquiv.mul_apply] using he
    exact (c.injective hh).symm
  have htw (v : V) : t (t v)=v := by
    have hh := congrArg (fun g : BinaryLinear.GL V => g v) ht
    exact hh
  have hdisplacement (v : V) : c (t v-v)=t v-v := hfixed _ (by
    rw [map_sub,htw]
    simp only [sub_eq_add_neg,binary_neg,add_comm])
  have hct (v : V) : t (c v)=c (t v) :=
    congrArg (fun g : BinaryLinear.GL V => g v) htc.eq
  have hcv (v : V) : c (c v-v)=c v-v := hfixed _ (by
    have hh := hdisplacement v
    rw [map_sub] at hh
    rw [map_sub,hct]
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      have he := sub_eq_sub_iff_add_eq_add.mp hh
      simpa only [add_comm] using he))
  have hc2 : c^2=1 := by
    ext v
    have he := hcv v
    rw [map_sub] at he
    have hh : c (c v)=v := by
      rw [sub_eq_add_neg,binary_neg,sub_eq_add_neg,binary_neg] at he
      exact add_right_cancel (by simpa only [add_comm] using he)
    exact hh
  have he := hc
  rw [pow_succ,hc2,one_mul] at he
  exact he

end BinaryLinear
