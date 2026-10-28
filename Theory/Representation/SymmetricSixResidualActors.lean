module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Elementary automorphisms of a symmetric-six action residual

Identify the actual solvable residual of an S6 linear group with its A6
subgroup through the given overgroup equivalence. The proved A6 automorphism
theorem puts every elementary two-subgroup of order at least eight in the
permutation-induced S6. Lifting that permutation back to the original linear
group gives its actual intertwining map. Transport of the A6 center removes
the residual center as well.

This result concerns the marked residual inclusion, not an arbitrary A6
module. Its degree-four symplectic application supplies the exceptional
model obstruction in Aschbacher--Smith G.10.15, printed p.363.
-/

public noncomputable section
open Subgroup AlternatingSix.ShadowLocal
namespace Representation.SymmetricSixResidualActors

private theorem residual_symmetricSix : solvableResidual (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply le_antisymm
  · exact (solvableResidual_le_derivedSeries 1).trans_eq
      (alternatingGroup.commutator_perm_eq (by simp))
  · exact le_solvableResidual_of_isPerfect _

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (D : Subgroup (V ≃ₗ[ZMod 2] V)) (e : D ≃* Equiv.Perm (Fin 6))

private def residualAlternatingSixEquiv : ((solvableResidual D).map D.subtype) ≃* A6 := by
  let : Finite D := Finite.of_injective e e.injective
  let a := (solvableResidual D).equivMapOfInjective D.subtype D.subtype_injective
  let b := e.subgroupMap (solvableResidual D)
  have hb : (solvableResidual D).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [map_solvableResidual_eq _ e.surjective, residual_symmetricSix]
  exact a.symm.trans (b.trans (MulEquiv.subgroupCongr hb))

private theorem residualAlternatingSixEquiv_coe (x : (solvableResidual D).map D.subtype) :
    (residualAlternatingSixEquiv D e x : Equiv.Perm (Fin 6)) =
      e ⟨x.val, by obtain ⟨y,_,h⟩ := x.property; rw [← h]; exact y.property⟩ := by
  let a := (solvableResidual D).equivMapOfInjective D.subtype D.subtype_injective
  change e (a.symm x).val = _
  have h := congrArg (fun y : (solvableResidual D).map D.subtype => y.val)
    (a.apply_symm_apply x)
  have h' : ((a.symm x).val : V ≃ₗ[ZMod 2] V) = x.val := h
  exact congrArg e (Subtype.ext h')

include e
/-- In an S6 action, the literal solvable residual is centerless, and every
member of an elementary order-at-least-eight automorphism subgroup of that
residual is realized by a linear intertwiner from the original S6 action. -/
theorem center_and_elementary_intertwiners :
    center ((solvableResidual D).map D.subtype) = ⊥ ∧
      ∀ E : Subgroup (MulAut ((solvableResidual D).map D.subtype)),
        IsElementaryAbelian 2 E → 8 ≤ Nat.card E →
        ∀ α ∈ E, ∃ c : V ≃ₗ[ZMod 2] V,
          ∀ k : (solvableResidual D).map D.subtype, ∀ v : V,
            c (k.val v) = (α k).val (c v) := by
  let K := (solvableResidual D).map D.subtype
  let f := residualAlternatingSixEquiv D e
  have hKD : K ≤ D := by
    rintro _ ⟨x,hx,rfl⟩
    exact x.property
  let inc : K →* D := Subgroup.inclusion hKD
  have hf (k : K) : (f k : Equiv.Perm (Fin 6)) = e (inc k) :=
    residualAlternatingSixEquiv_coe D e k
  constructor
  · apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply f.injective
    have hz := (centerCongr f ⟨x,hx⟩).property
    change f x ∈ center A6 at hz
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)), mem_bot] at hz
    simpa using hz
  · intro E hE hcard α hα
    let t := MulAut.congr f
    let E' := E.map t.toMonoidHom
    let : IsElementaryAbelian 2 E := hE
    let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
    have hcard' : 8 ≤ Nat.card E' := by
      rw [Subgroup.card_map_of_injective t.injective]
      exact hcard
    have ha' := elementary_le_natural_of_eight_le E' hcard'
      (Subgroup.mem_map_of_mem t.toMonoidHom hα)
    obtain ⟨σ,hσ⟩ := ha'
    let d := e.symm σ
    refine ⟨d.val, ?_⟩
    intro k v
    have hh := congrArg (fun β : MulAut A6 => (β (f k) : Equiv.Perm (Fin 6))) hσ
    have heq : σ * e (inc k) * σ⁻¹ = e (inc (α k)) := by
      change σ * (f k : Equiv.Perm (Fin 6)) * σ⁻¹ =
        (f (α (f.symm (f k))) : Equiv.Perm (Fin 6)) at hh
      simpa only [f.symm_apply_apply, hf] using hh
    have hd : d * inc k = inc (α k) * d := by
      apply e.injective
      rw [map_mul, map_mul]
      dsimp only [d]
      rw [e.apply_symm_apply]
      exact mul_inv_eq_iff_eq_mul.mp heq
    exact LinearEquiv.congr_fun (congrArg Subtype.val hd) v

end Representation.SymmetricSixResidualActors
