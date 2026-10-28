module
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.DiagramEquivalence

/-!
# Diagram obstruction for representations extending the Hermitian action

An ambient representation supplies an invertible operator for each actor.
Transporting that operator through actual Hermitian coordinates gives the
intertwiner used by the computed PSL₃(4) normalizer. Thus an automorphism
implemented on this module preserves both geometric parabolic types.
The conclusion is independent of the field and quotient marking.

This supplies the nine-dimensional constituent obstruction at the end of
Aschbacher--Smith 5.1.23, printed p.646 of `refs/quasithin.pdf`. Selection
and invariance of the constituent are separate from this normalizer argument.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Representation.HermitianTensorThree.ImageOuter
variable {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]

/-- The implementing operator is constructed from the same ambient representation. -/
theorem diagram_trivial_of_representation
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X)
    (j : K ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1)
    (hc : ∀ k : K, ∀ w : W, c (ρ k w) = projectiveAction (j k) (c w))
    (t : X) (a : MulAut K) (b : MulAut PSL(3,E 1))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, j (a k) = b (j k)) : b ∈ diagramTrivial (E 1) := by
  let v : W ≃ₗ[ZMod 2] W := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  let u := c.symm.trans (v.trans c)
  apply diagram_trivial_of_intertwiner u b
  intro x
  obtain ⟨k,rfl⟩ := j.surjective x
  apply LinearEquiv.ext
  intro y
  obtain ⟨w,rfl⟩ := c.surjective y
  change c (ρ t (c.symm (projectiveAction (j k) (c (ρ t⁻¹ (c.symm (c w))))))) =
    projectiveAction (b (j k)) (c w)
  rw [c.symm_apply_apply,← hc,c.symm_apply_apply,← hb,← hc]
  apply congrArg c
  rw [ha,map_mul,map_mul]
  rfl

/-- A genuine diagram actor excludes Hermitian coordinates in every marking. -/
theorem not_hermitian_of_diagram_action
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F) :
    ¬ ∃ (j : K ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w : W, c (ρ k w) = projectiveAction (j k) (c w) := by
  rintro ⟨j,c,hc⟩
  let i := e.symm.trans j
  let b' := MulAut.congr i b
  have hb' (k : K) : j (a k) = b' (j k) := by
    change j (a k) = j (e.symm (b (e (j.symm (j k)))))
    rw [j.symm_apply_apply,← hb,e.symm_apply_apply]
  exact hd (diagramTrivial_of_equiv_four hF (card_E 1) i b
    (diagram_trivial_of_representation ρ K j c hc t a b' ha hb'))
end Representation.HermitianTensorThree.ImageOuter
