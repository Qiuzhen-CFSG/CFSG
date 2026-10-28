module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.BlockExtensions
public import Mathlib.LinearAlgebra.Projection

/-!
# Recovering block coordinates from the actual invariant filtration

Choose a vector-space complement to an invariant submodule. Its quotient map
identifies the complement with the actual quotient. Given representation
equivalences from these two layers to the concrete constituents, conjugating
the whole action gives an upper triangular block action. Its cross block
satisfies the cocycle identity directly from the multiplication law.

The complement is only linear: this construction makes no splitting or
semisimplicity assumption and retains every nonsplit extension. It supplies
the coordinate step for James (1973), Lemma 8.3, as used in the local SL₃(4)
catalogue for Aschbacher–Smith H.12.1, printed pp.393–394.
-/

public noncomputable section
namespace Representation.SL3FourLocalCatalogue
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U)

private lemma exists_layer_coordinates (N : Subrepresentation σ) {a b : Constituent}
    (ea : N.toRepresentation.Equiv (constituent a))
    (eb : N.quotientRepresentation.Equiv (constituent b)) :
    ∃ e : U ≃ₗ[ZMod 2] W × W,
      (∀ x : N.toSubmodule, e x = (ea x, 0)) ∧
      (∀ x : U, (e x).2 = eb (N.toSubmodule.mkQ x)) := by
  obtain ⟨Q, hQ⟩ := N.toSubmodule.exists_isCompl
  let d := N.toSubmodule.prodEquivOfIsCompl Q hQ
  let q := N.toSubmodule.quotientEquivOfIsCompl Q hQ
  let e := d.symm.trans (ea.toLinearEquiv.prodCongr (q.symm.trans eb.toLinearEquiv))
  refine ⟨e, ?_, ?_⟩
  · intro x
    change (ea (d.symm x).1, eb (q.symm (d.symm x).2)) = (ea x, 0)
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp
  · intro x
    change eb (q.symm (d.symm x).2) = eb (N.toSubmodule.mkQ x)
    congr 1
    change N.toSubmodule.mkQ ((d.symm x).2 : U) = N.toSubmodule.mkQ x
    have hx : ((d.symm x).1 : U) + ((d.symm x).2 : U) = x := d.apply_symm_apply x
    calc
      _ = N.toSubmodule.mkQ (((d.symm x).1 : U) + ((d.symm x).2 : U)) := by
        rw [map_add, show N.toSubmodule.mkQ ((d.symm x).1 : U) = 0 from
          (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr (d.symm x).1.property,
          zero_add]
      _ = _ := congrArg N.toSubmodule.mkQ hx

/-- A genuine invariant submodule and quotient identified with the constituents
supply block coordinates for the entire action, without an equivariant section. -/
theorem exists_block_equiv (N : Subrepresentation σ) {a b : Constituent}
    (ea : N.toRepresentation.Equiv (constituent a))
    (eb : N.quotientRepresentation.Equiv (constituent b)) :
    ∃ c : BlockCocycle a b, Nonempty (σ.Equiv c.representation) := by
  obtain ⟨e, heN, heQ⟩ := exists_layer_coordinates σ N ea eb
  let τ : Representation (ZMod 2) SL (W × W) := e.conjRingEquiv.toMonoidHom.comp σ
  have ht (g : SL) (v : W × W) : τ g v = e (σ g (e.symm v)) := rfl
  have hN (g : SL) (x : W) : τ g (x, 0) = (constituent a g x, 0) := by
    have hx : e.symm (x, 0) = (ea.symm x : U) := by
      apply e.injective
      rw [e.apply_symm_apply, heN]
      simp
    rw [ht, hx]
    change e (N.toRepresentation g (ea.symm x)) = _
    rw [heN]
    have hi := LinearMap.congr_fun (ea.isIntertwining' g) (ea.symm x)
    change ea (N.toRepresentation g (ea.symm x)) = constituent a g (ea (ea.symm x)) at hi
    simpa using congrArg (fun y : W => (y, (0 : W))) hi
  have hQ (g : SL) (v : W × W) : (τ g v).2 = constituent b g v.2 := by
    rw [ht, heQ, ← Subrepresentation.quotientRepresentation_mk]
    have hi := LinearMap.congr_fun (eb.isIntertwining' g) (N.toSubmodule.mkQ (e.symm v))
    change eb (N.quotientRepresentation g (N.toSubmodule.mkQ (e.symm v))) =
      constituent b g (eb (N.toSubmodule.mkQ (e.symm v))) at hi
    rw [hi, ← heQ, e.apply_symm_apply]
  let c : SL → W →ₗ[ZMod 2] W := fun g =>
    (LinearMap.fst (ZMod 2) W W).comp ((τ g).comp (LinearMap.inr (ZMod 2) W W))
  have hc (g : SL) (v : W × W) :
      τ g v = (constituent a g v.1 + c g v.2, constituent b g v.2) := by
    apply Prod.ext
    · have hv : v = (v.1, 0) + (0, v.2) := by simp
      conv_lhs => rw [hv, map_add, hN]
      rfl
    · exact hQ g v
  let C : BlockCocycle a b := {
    value := c
    one := by
      apply LinearMap.ext
      intro v
      change (τ 1 (0, v)).1 = 0
      simp
    mul := fun g h => by
      apply LinearMap.ext
      intro v
      have hm := LinearMap.congr_fun (τ.map_mul g h) (0, v)
      change τ (g * h) (0, v) = τ g (τ h (0, v)) at hm
      have hf := congrArg Prod.fst hm
      simp only [hc, map_zero, zero_add] at hf
      exact hf }
  refine ⟨C, ⟨.mk e (fun g => ?_)⟩⟩
  apply LinearMap.ext
  intro v
  change e (σ g v) = (constituent a g (e v).1 + c g (e v).2,
    constituent b g (e v).2)
  simpa only [ht, e.symm_apply_apply] using hc g (e v)
end Representation.SL3FourLocalCatalogue
