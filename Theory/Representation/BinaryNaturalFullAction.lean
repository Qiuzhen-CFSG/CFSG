module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Module.ZMod

/-!
# Full automorphisms of a binary natural module

Every automorphism of the multiplicative additive group of a binary vector
space is linear. Its determinant is one, so it is the action of an actual
special-linear matrix. The pointwise equation retains the original
multiplicative automorphism and the standard natural representation.

Source application: Aschbacher--Smith, 12.2.25, printed p.805. This supplies
the full action needed to identify the normalizer of the chosen module.
-/

public section
namespace Representation
theorem specialLinearNatural_binary_full (n : ℕ)
    (a : MulAut (Multiplicative (Fin n → ZMod 2))) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      ∀ v : Multiplicative (Fin n → ZMod 2),
        Multiplicative.ofAdd (specialLinearNatural n g v.toAdd) = a v := by
  let b : (Fin n → ZMod 2) ≃+ (Fin n → ZMod 2) := AddEquiv.toMultiplicative.symm a
  let c : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofBijective (b.toAddMonoidHom.toZModLinearMap 2) b.bijective
  refine ⟨(BinaryLinear.OuterCyclic.slEquivLinear n).symm c, ?_⟩
  intro v
  have he := congrArg (fun f : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) => f v.toAdd)
    ((BinaryLinear.OuterCyclic.slEquivLinear n).apply_symm_apply c)
  exact congrArg Multiplicative.ofAdd he
end Representation
