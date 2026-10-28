module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural

/-!
# Natural recognition in full binary linear degree

A faithful degree-n binary action of a group isomorphic to SL_n(2) is
natural up to a group automorphism. Choose binary coordinates, embed the
actor into GL_n(2), and use equality of finite orders to obtain surjectivity.
The binary determinant is automatically one. The resulting equivalence
retains the original action and its explicit coordinate intertwiner.

Source application: Aschbacher–Smith K.3.2 and B.4.2(9), the binary natural
four- and five-dimensional cases. No module classification is assumed.
-/

public section
namespace Representation.BinaryFullLinearRecognition
open scoped MatrixGroups

/-- Faithfulness and the natural dimension determine the actual binary action. -/
theorem exists_natural_equiv {L V : Type*} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) L V)
    (hf : Function.Injective σ) {n : ℕ}
    (e₀ : L ≃* SL(n,ZMod 2)) (hd : Module.finrank (ZMod 2) V = n) :
    ∃ (e : L ≃* SL(n,ZMod 2)) (f : V ≃ₗ[ZMod 2] (Fin n → ZMod 2)),
      ∀ l v, f (σ l v) = (e l).val.mulVec (f v) := by
  classical
  let f : V ≃ₗ[ZMod 2] (Fin n → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let a := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).trans
    (BinaryLinear.OuterCyclic.slEquivLinear n).symm
  let φ : L →* SL(n,ZMod 2) := a.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv f).toMonoidHom.comp σ.asGroupHom)
  have hφ : Function.Injective φ := by
    apply a.injective.comp
    apply (LinearMap.GeneralLinearGroup.congrLinearEquiv f).injective.comp
    intro x y h
    exact hf (congrArg Units.val h)
  have hs : Function.Surjective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, Nat.card_congr e₀.toEquiv⟩ |>.2
  let e := MulEquiv.ofBijective φ ⟨hφ,hs⟩
  refine ⟨e,f,?_⟩
  intro l v
  have h := BinaryLinear.OuterCyclic.slEquivLinear_apply n (e l) (f v)
  rw [show BinaryLinear.OuterCyclic.slEquivLinear n (e l) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2))
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv f) (σ.asGroupHom l)) by
        exact (BinaryLinear.OuterCyclic.slEquivLinear n).apply_symm_apply _] at h
  simpa [Representation.asGroupHom_apply] using h

end Representation.BinaryFullLinearRecognition
