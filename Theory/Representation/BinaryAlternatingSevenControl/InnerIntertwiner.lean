module
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer

/-!
# Inner automorphisms compatible with a faithful binary A₇ four-space

An intertwining linear automorphism normalizes the actual A₇ image.
Self-normalization in GL₄(2) makes that linear map an A₇ operator; faithfulness
then identifies the group automorphism with inner conjugation. This works for
both orientations of the exceptional four-space.

Source: Aschbacher–Smith C.1.23(2), printed p.130, and the original 15.3.21
second-choice application, printed p.1127.
-/
public section
open Subgroup
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem inner_of_intertwiner (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (α : MulAut A7) (f : V ≃ₗ[ZMod 2] V)
    (he : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    ∃ g : A7, α = MulAut.conj g := by
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv f
  have hu (g : A7) : u * ρ.asGroupHom g * u⁻¹ = ρ.asGroupHom (α g) := by
    apply Units.ext
    ext v
    exact (he g (f.symm v)).trans (congrArg (ρ (α g)) (f.apply_symm_apply v))
  have hn : u ∈ normalizer (Representation.BinaryOffender.actionImage ρ :
      Set (Module.End (ZMod 2) V)ˣ) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨α g,(hu g).symm⟩
    · rintro ⟨g,hg⟩
      refine ⟨α.symm g,?_⟩
      have hh := hu (α.symm g)
      rw [α.apply_symm_apply] at hh
      have := hh.trans hg
      exact (mul_left_cancel (mul_right_cancel this))
  rw [actionImage_self_normalizing ρ hf hd] at hn
  obtain ⟨g,hg⟩ := hn
  refine ⟨g,?_⟩
  apply MulEquiv.ext
  intro k
  apply hf
  have hh : ρ.asGroupHom (α k) = ρ.asGroupHom (MulAut.conj g k) := by
    rw [←hu k,←hg]
    simp only [MulAut.conj_apply,map_mul,map_inv]
  exact congrArg Units.val hh
end Representation.BinaryAlternatingSevenControl
