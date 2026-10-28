module

public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# A cubic element in a small natural subspace stabilizer

Every two- or three-dimensional subspace of the native binary natural module
has a stabilizing element of exact order three which acts nontrivially on it.
Choose a cubic automorphism of the subspace and extend it by the identity on
a complement. The binary SL/GL comparison preserves this literal action.

This finite linear statement does not assert the outstanding source lift or
identify the original denominator with the kernel's shear value space.
-/

public section
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

private noncomputable def extendOnComplement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Submodule (ZMod 2) W) (h : IsCompl P Q) :
    BinaryLinear.GL P →* BinaryLinear.GL W where
  toFun a :=
    (P.prodEquivOfIsCompl Q h).symm.trans
      ((a.prodCongr (LinearEquiv.refl (ZMod 2) Q)).trans (P.prodEquivOfIsCompl Q h))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.coe_one, id_eq, LinearEquiv.refl_apply, Prod.mk.eta,
      LinearEquiv.apply_symm_apply]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.mul_apply, LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]

private theorem extendOnComplement_apply
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Submodule (ZMod 2) W) (h : IsCompl P Q)
    (a : BinaryLinear.GL P) (v : P) :
    extendOnComplement P Q h a v = (a v : W) := by
  simp [extendOnComplement]

/-- A plane or three-space in the binary natural module has a nontrivial
cubic element in its setwise stabilizer. -/
theorem exists_order_three_moving_subspace
    (n : ℕ) (P : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hP : Module.finrank (ZMod 2) P = 2 ∨ Module.finrank (ZMod 2) P = 3) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      orderOf g = 3 ∧
      P.map (Representation.specialLinearNatural n g) = P ∧
      ∃ v ∈ P, Representation.specialLinearNatural n g v ≠ v := by
  classical
  let : Finite P := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL P) :=
    Finite.of_injective (fun a : BinaryLinear.GL P => (a : P → P)) DFunLike.coe_injective
  have hdiv : 3 ∣ Nat.card (BinaryLinear.GL P) := by
    rcases hP with hP | hP
    · rw [BinaryLinear.card_GL_of_finrank hP]
      norm_num [BinaryLinear.order, Fin.prod_univ_succ]
    · rw [BinaryLinear.card_GL_of_finrank hP]
      norm_num [BinaryLinear.order, Fin.prod_univ_succ]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := BinaryLinear.GL P) 3 hdiv
  obtain ⟨Q, hQ⟩ := exists_isCompl P
  let f := extendOnComplement P Q hQ
  have hf : Function.Injective f := by
    intro a b hab
    apply LinearEquiv.ext
    intro v
    apply Subtype.coe_injective
    have he := congrArg (fun c : BinaryLinear.GL (Fin n → ZMod 2) => c v) hab
    simpa only [f, extendOnComplement_apply] using he
  let g := (BinaryLinear.OuterCyclic.slEquivLinear n).symm (f a)
  have hg (v : Fin n → ZMod 2) :
      Representation.specialLinearNatural n g v = f a v := by
    change BinaryLinear.OuterCyclic.slEquivLinear n g v = f a v
    rw [MulEquiv.apply_symm_apply]
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, orderOf_injective f hf, ha]
  · apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      rw [hg, show f a w = (a ⟨w, hw⟩ : Fin n → ZMod 2) from
        extendOnComplement_apply P Q hQ a ⟨w, hw⟩]
      exact (a ⟨w, hw⟩).property
    · intro v hv
      refine ⟨(a.symm ⟨v, hv⟩ : Fin n → ZMod 2), (a.symm ⟨v, hv⟩).property, ?_⟩
      rw [hg, extendOnComplement_apply]
      simp
  · have hne : a ≠ 1 := by
      intro he
      simp [he] at ha
    have hm : ∃ v : P, a v ≠ v := by
      by_contra h
      apply hne
      apply LinearEquiv.ext
      intro v
      exact not_not.mp (not_exists.mp h v)
    obtain ⟨v, hv⟩ := hm
    refine ⟨v, v.property, ?_⟩
    rw [hg, extendOnComplement_apply]
    exact fun he => hv (Subtype.coe_injective he)

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
