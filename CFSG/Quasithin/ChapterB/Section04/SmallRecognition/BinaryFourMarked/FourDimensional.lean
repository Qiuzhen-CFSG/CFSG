module

public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Four-dimensional recognition with a fixed binary L₄ marking

A faithful action on a four-space, conjugated into the standard coordinates,
is an injective endomorphism of the finite group GL₄(2), hence an automorphism.
The proved inner/graph theorem removes its inner part. The dot-product pairing
identifies the remaining inverse transpose with the literal dual action.
Both alternatives retain the originally supplied group equivalence.

This is the degree-four recognition step in Aschbacher--Smith B.4.2(9),
used in the proof of 13.8.25, printed pp.960--961. The actor and vector-space
universes are independent; no irreducibility or changed marking is assumed.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
open Representation BinaryLinear.OuterCyclic
abbrev Four := Fin 4 → ZMod 2
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def natural (eH : H ≃* BinaryLinear.GL Four) : Representation (ZMod 2) H Four where
  toFun g := (eH g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by simp

private theorem pairing_graph (k : BinaryLinear.GL Four) (v : Four) :
    dotProductEquiv (ZMod 2) (Fin 4) (graphLinear 4 k v) =
      (dotProductEquiv (ZMod 2) (Fin 4) v).comp k.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change dotProduct (graphLinear 4 k v) x = dotProduct v (k.symm x)
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct k v (k⁻¹ x)

/-- Every faithful representation in degree four is natural or dual for the
supplied marking. The action automorphism is inner or inverse-transpose inner. -/
theorem natural_or_dual_of_finrank_four [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (eH : H ≃* BinaryLinear.GL Four)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    (∃ e : V ≃ₗ[ZMod 2] Four, ∀ g v, e (ρ g v) = eH g (e v)) ∨
    (∃ e : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Four,
      ∀ g v, e (ρ g v) = (natural eH).dual g (e v)) := by
  let : Finite (BinaryLinear.GL Four) :=
    Finite.of_injective (fun g : BinaryLinear.GL Four => (g : Four → Four)) DFunLike.coe_injective
  let e₀ : V ≃ₗ[ZMod 2] Four := LinearEquiv.ofFinrankEq _ _ (by simpa [Four] using hd)
  let C := (LinearMap.GeneralLinearGroup.congrLinearEquiv e₀).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four)
  let f : BinaryLinear.GL Four →* BinaryLinear.GL Four :=
    C.toMonoidHom.comp (ρ.asGroupHom.comp eH.symm.toMonoidHom)
  have hf' : Function.Injective f := by
    intro x y hxy
    apply eH.symm.injective
    apply hf
    exact congrArg Units.val (C.injective hxy)
  let a : MulAut (BinaryLinear.GL Four) :=
    MulEquiv.ofBijective f ⟨hf', Finite.surjective_of_injective hf'⟩
  have ha (g : H) (v : V) : e₀ (ρ g v) = a (eH g) (e₀ v) := by
    change e₀ (ρ g v) = e₀ (ρ (eH.symm (eH g)) (e₀.symm (e₀ v)))
    rw [eH.symm_apply_apply, e₀.symm_apply_apply]
  obtain ⟨k, hk | hk⟩ := BinaryLinear.ElementaryOuterSylow.inner_graph (by decide : 2 ≤ 4) a
  · refine Or.inl ⟨e₀.trans k.symm, fun g v => ?_⟩
    simp only [LinearEquiv.trans_apply, ha, hk, MulAut.conj_apply,
      LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  · refine Or.inr ⟨e₀.trans ((graphLinear 4 k).symm.trans
        (dotProductEquiv (ZMod 2) (Fin 4))), fun g v => ?_⟩
    simp only [LinearEquiv.trans_apply, ha, hk, MulAut.mul_apply, MulAut.conj_apply,
      map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
    rw [pairing_graph]
    change _ = (dotProductEquiv (ZMod 2) (Fin 4) ((graphLinear 4 k).symm (e₀ v))).comp
      (eH g⁻¹).toLinearMap
    rw [map_inv]
    rfl

end CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
