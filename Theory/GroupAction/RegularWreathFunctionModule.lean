module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Algebra.Group.Action.Pi

/-!
# The regular wreath action on a function module

A distributive action of D on a group V gives an action of the regular
wreath product D ≀ᵣ Q on Q → V. The shift selects coordinate q⁻¹ * i,
then the base actor at i acts on that value. This is the function-module
realization of the standard regular wreath action, using Mathlib's literal
wreath multiplication and the pointwise group structure on functions.

The action is an exposed, named instance-valued definition rather than a
global instance, so a consumer explicitly retains this exact action. Its
coordinate equation is definitional. Constant functions show that equal
actions have equal base actors when D acts faithfully; a nontrivial function
supported at one coordinate then distinguishes the shifts. This proves
faithfulness when V is nontrivial, with no finiteness assumptions.

The construction supplies the intrinsic imprimitive module used in the
one-seven and local wreath-module arguments of Stellmacher (1.7) and (9.3).
Only the standard wreath-product definition and group-action axioms are used.
-/

namespace RegularWreathProduct

/-- The literal coordinate action, installed explicitly by each consumer. -/
@[expose, instance_reducible] public def functionModule
    (D Q V : Type*) [Group D] [Group Q] [Group V] [MulDistribMulAction D V] :
    MulDistribMulAction (D ≀ᵣ Q) (Q → V) where
  smul w v i := w.left i • v (w.right⁻¹ * i)
  one_smul v := by
    funext i
    change (1 : D) • v ((1 : Q)⁻¹ * i) = v i
    simp
  mul_smul a b v := by
    funext i
    change (a.left i * b.left (a.right⁻¹ * i)) • v ((a.right * b.right)⁻¹ * i) =
      a.left i • (b.left (a.right⁻¹ * i) • v (b.right⁻¹ * (a.right⁻¹ * i)))
    simp [mul_smul, mul_assoc]
  smul_one w := by funext i; exact smul_one _
  smul_mul w v u := by funext i; exact smul_mul' _ _ _

/-- The shift is applied before the base actor at the output coordinate. -/
public theorem functionModule_smul_apply
    {D Q V : Type*} [Group D] [Group Q] [Group V] [MulDistribMulAction D V]
    (w : D ≀ᵣ Q) (v : Q → V) (i : Q) :
    letI := functionModule D Q V
    (w • v) i = w.left i • v (w.right⁻¹ * i) := rfl

/-- Faithfulness of the coordinate action, with the precise named action installed. -/
public theorem functionModule_faithful
    (D Q V : Type*) [Group D] [Group Q] [Group V] [MulDistribMulAction D V]
    [FaithfulSMul D V] [Nontrivial V] :
    letI := functionModule D Q V
    FaithfulSMul (D ≀ᵣ Q) (Q → V) := by
  let _ := functionModule D Q V
  classical
  constructor
  intro a b hab
  have hleft : a.left = b.left := by
    funext i
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    exact congrFun (hab (fun _ => v)) i
  have hright : a.right = b.right := by
    by_contra hne
    have hinv : b.right⁻¹ ≠ a.right⁻¹ := by
      intro he
      exact hne (inv_injective he).symm
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    let f : Q → V := fun q => if q = a.right⁻¹ then v else 1
    have he := congrFun (hab f) (1 : Q)
    change a.left 1 • f (a.right⁻¹ * 1) = b.left 1 • f (b.right⁻¹ * 1) at he
    rw [hleft] at he
    have hf := MulAction.injective (b.left 1) he
    exact hv (by simpa only [mul_one, f, if_pos rfl, if_neg hinv] using hf)
  exact RegularWreathProduct.ext hleft hright

end RegularWreathProduct
