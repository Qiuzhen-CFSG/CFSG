module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

universe u

namespace Theory.AlgebraicGroup.Bor1

/-- The augmentation extended from an algebra to the residue field at its
kernel. -/
@[expose] public noncomputable def augmentedLocalizationResidueAlgHom
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (e : B →ₐ[k] k) (he : Function.Surjective e) :
    letI : (RingHom.ker e).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective e he).isPrime
    (RingHom.ker e).ResidueField →ₐ[k] k := by
  let m := RingHom.ker e
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e he
  letI : m.IsPrime := inferInstance
  exact Ideal.ResidueField.liftₐ m e le_rfl (by
    intro x hx
    change IsUnit (e x)
    exact isUnit_iff_ne_zero.mpr (by
      intro hz
      exact hx hz))

/-- The residue field at the kernel of a surjective augmentation to a field
is canonically that field. -/
@[expose] public noncomputable def augmentedLocalizationResidueAlgEquiv
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (e : B →ₐ[k] k) (he : Function.Surjective e) :
    letI : (RingHom.ker e).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective e he).isPrime
    (RingHom.ker e).ResidueField ≃ₐ[k] k := by
  let m := RingHom.ker e
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e he
  letI : m.IsPrime := inferInstance
  let f : m.ResidueField →ₐ[k] k :=
    augmentedLocalizationResidueAlgHom e he
  apply AlgEquiv.ofBijective f
  constructor
  · exact f.toRingHom.injective
  · intro c
    exact ⟨algebraMap k m.ResidueField c, f.commutes c⟩

set_option linter.style.haveILetI false in
@[simp] public theorem augmentedLocalizationResidueAlgEquiv_algebraMap
    {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (e : B →ₐ[k] k) (he : Function.Surjective e) (b : B) :
    letI : (RingHom.ker e).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective e he).isPrime
    augmentedLocalizationResidueAlgEquiv e he
        (algebraMap B (RingHom.ker e).ResidueField b) = e b := by
  letI : (RingHom.ker e).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective e he
  letI : (RingHom.ker e).IsPrime := inferInstance
  change augmentedLocalizationResidueAlgHom e he
    (algebraMap B (RingHom.ker e).ResidueField b) = e b
  exact Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ _

end Theory.AlgebraicGroup.Bor1
