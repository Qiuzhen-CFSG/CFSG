module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine

/-!
# Killing a power in the original polar kernel

A power whose quotient is one belongs to the actual kernel and centralizes
its own base. A fixed-point-free quotient action therefore forces that power
to be one, without choosing a complement or altering the lifted element.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine

/-- A fixed-point-free polar quotient kills the indicated power of the same
original element, with its full original kernel coordinates retained. -/
theorem power_eq_one_of_quotient_power_of_fixed_free {D : Type*} [Group D]
    (q : D →* A6) (k : q.ker≃*Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a)=
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (x : D) (m : Nat) (hpow : (q x)^m=1)
    (hfree : ∀ v : NaturalModule, polarAction (q x).val v=v → v=0) :
    x^m=1 := by
  let a : q.ker := ⟨x^m,by rw [MonoidHom.mem_ker,map_pow,hpow]⟩
  have hac : MulAut.conjNormal x a=a := by
    apply Subtype.ext
    change x*x^m*x⁻¹=x^m
    rw [(Commute.self_pow x m).eq,mul_inv_cancel_right]
  have hfix : polarAction (q x).val (k a).toAdd=(k a).toAdd := by
    have hh := hk x a
    rw [hac] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  have ha : a=1 := k.injective (by
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hfree (k a).toAdd hfix)
  exact congrArg Subtype.val ha

end Theory.SpecificGroups.SymmetricSix.PolarAffine
