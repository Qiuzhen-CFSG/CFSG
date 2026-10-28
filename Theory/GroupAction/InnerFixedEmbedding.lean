module
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Lifting commuting inner actors to the actual fixed group

In a centerless group, the inner-action map is injective. An inner action
therefore lifts uniquely to the original group; if it commutes with an
automorphism, its lift belongs to that automorphism's fixed group. The
construction preserves faithfulness and the literal conjugation equation.

This elementary transport is used in the Theorem C inspection in
Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/
public section
namespace MulAut
open Subgroup
variable {G P : Type*} [Group G] [Group P]

/-- A faithful inner action commuting with an automorphism embeds in its literal fixed group. -/
theorem exists_injective_fixed_lift (hz : center G = ⊥) (a : MulAut G)
    (ρ : P →* MulAut G) (hρ : Function.Injective ρ)
    (hi : ρ.range ≤ innerSubgroup G)
    (hc : ∀ x, a * ρ x = ρ x * a) :
    ∃ f : P →* a.fixedSubgroup, Function.Injective f ∧
      ∀ x, conj (f x).val = ρ x := by
  let e : G ≃* innerSubgroup G :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let j := ρ.codRestrict (innerSubgroup G) (fun x => hi ⟨x,rfl⟩)
  let k := e.symm.toMonoidHom.comp j
  have hk (x : P) : conj (k x) = ρ x :=
    congrArg Subtype.val (e.apply_symm_apply (j x))
  let f : P →* a.fixedSubgroup := k.codRestrict _ (fun x => by
    rw [mem_fixedSubgroup]
    apply MulAut.conj_injective_of_center_eq_bot hz
    have he : a * conj (k x) * a⁻¹ = conj (a (k x)) := by
      ext y
      simp
    rw [←he,hk,hc,mul_assoc,mul_inv_cancel,mul_one])
  refine ⟨f,?_,hk⟩
  intro x y he
  apply hρ
  exact (hk x).symm.trans ((congrArg (fun z : a.fixedSubgroup => conj z.val) he).trans (hk y))
end MulAut
