module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.FixedFreePower

/-!
# Killing a kernel power using a different fixed-free actor

The same original kernel calculation works when the power defect is known to
centralize a fixed-point-free actor.  This is the precise source-side bridge
needed for the remaining D-relators; it introduces no section or splitting.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine

theorem power_eq_one_of_quotient_power_of_centralizer_fixed_free
    {D : Type*} [Group D]
    (q : D →* A6) (k : q.ker≃*Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a)=
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (x a : D) (m : Nat)
    (hpow : (q x)^m=1)
    (hfree : ∀ v : NaturalModule,
      polarAction (q a).val v=v → v=0)
    (hcomm : Commute (x^m) a) : x^m=1 := by
  let z : q.ker := ⟨x^m,by rw [MonoidHom.mem_ker,map_pow,hpow]⟩
  have hz : MulAut.conjNormal a z=z := by
    apply Subtype.ext
    change a*x^m*a⁻¹=x^m
    exact (hcomm.eq ▸ by simp)
  have hfix : polarAction (q a).val (k z).toAdd=(k z).toAdd := by
    have hh := hk a z
    rw [hz] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  have hz1 : z=1 := k.injective (by
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hfree (k z).toAdd hfix)
  exact congrArg Subtype.val hz1

end Theory.SpecificGroups.SymmetricSix.PolarAffine
