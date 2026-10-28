module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.GroupTheory.SplitExtensionGivenComplement

/-!
# The affine group for the literal alternating-six polar action

The action uses the existing six-letter polar operators on the binary
four-space. Split coordinates preserve an original quotient, every element
of its full kernel, and a specified actual complement.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Subgroup

/- The additive polar action is already available for the six-letter group.
We transport it to the multiplicative wrapper used by the extension API. -/
noncomputable instance polarMultiplicativeAction :
    MulDistribMulAction S6 (Multiplicative NaturalModule) where
  smul g v := Multiplicative.ofAdd (polarAction g v.toAdd)
  one_smul v := by
    exact congrArg Multiplicative.ofAdd (polarAction_one v.toAdd)
  mul_smul g h v := by
    exact congrArg Multiplicative.ofAdd (polarAction_mul g h v.toAdd)
  smul_one g := by
    exact congrArg Multiplicative.ofAdd (polarAction_zero g)
  smul_mul g v w := by
    exact congrArg Multiplicative.ofAdd (polarAction_add g v.toAdd w.toAdd)

/- The literal action of A₆ is the restriction of this six-letter action. -/
def action : A6→*MulAut (Multiplicative NaturalModule) :=
  (MulDistribMulAction.toMulAut S6 (Multiplicative NaturalModule)).comp A6.subtype

@[simp] theorem action_apply (g : A6) (v : Multiplicative NaturalModule) :
    action g v = Multiplicative.ofAdd (polarAction g.val v.toAdd) := rfl

abbrev Model := Multiplicative NaturalModule ⋊[action] A6

/-- Marked affine coordinates on the original group preserve its original
quotient, full kernel and chosen complement exactly. -/
theorem exists_original_coordinates {D : Type*} [Group D]
    (q : D→*A6) (hq : Function.Surjective q)
    (k : q.ker≃*Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker),k (MulAut.conjNormal g a)=
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (K : Subgroup D) (hK : q.ker.IsComplement' K) :
    ∃ e : D≃*Model,
      (∀ g,(e g).right=q g) ∧
      (∀ a : q.ker,e a=SemidirectProduct.inl (k a)) ∧
      (∀ a : K,e a=SemidirectProduct.inr (q a)) ∧
      K.map e.toMonoidHom=(SemidirectProduct.inr:A6→*Model).range := by
  apply exists_marked_semidirect_equiv_of_given_complement q hq k action ?_ K hK
  intro g a
  simpa only [action_apply] using hk g a

end Theory.SpecificGroups.SymmetricSix.PolarAffine
