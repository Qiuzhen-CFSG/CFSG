module

public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Natural PSL₃(2) coordinates and contragredient transport

The model records actual group and linear equivalences, with their intertwining
identity. Its group carrier is matrix PSL₃(2); the action uses the proved
canonical comparison with SL₃(2). Transporting the explicit trace obstruction
proves non-self-duality. Dual coordinates retain the same actor isomorphism.

The model is a conclusion of recognition, not a recognition theorem.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.6 and the
constituent argument in 15.3.58, printed p.1149.
-/

@[expose] public section

namespace BinaryLinearThree.AutomorphismAction
open Representation

variable {A V : Type*} [_root_.Group A] [AddCommGroup V] [Module (ZMod 2) V]

theorem not_self_dual_of_natural_coordinates
    (ρ : Representation (ZMod 2) A V) (eA : A ≃* Group)
    (E : V ≃ₗ[ZMod 2] Vector)
    (hE : ∀ a v, E (ρ a v) = W (eA a) (E v)) :
    ¬ Nonempty (Representation.Equiv ρ ρ.dual) := by
  rintro ⟨e⟩
  apply natural_not_equiv_dual
  have hs (a : Group) (v : Vector) :
      E.symm (W a v) = ρ (eA.symm a) (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply, hE, eA.apply_symm_apply, E.apply_symm_apply]
  refine ⟨{ toLinearEquiv := E.symm.trans (e.toLinearEquiv.trans E.symm.dualMap)
            isIntertwining' := ?_ }⟩
  intro a
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change e (E.symm (W a v)) (E.symm w) =
    e (E.symm v) (E.symm (W a⁻¹ w))
  rw [hs, hs]
  have he := LinearMap.congr_fun (e.isIntertwining' (eA.symm a)) (E.symm v)
  simpa only [LinearMap.comp_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, map_inv, Representation.Equiv.coe_toLinearMap] using
    congrArg (fun f : Module.Dual (ZMod 2) V => f (E.symm w)) he

end BinaryLinearThree.AutomorphismAction

namespace BinaryLinearThree
variable {A V : Type*} [_root_.Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual group and module coordinates for a natural binary three-space. -/
structure NaturalModel (ρ : Representation (ZMod 2) A V) where
  actor : A ≃* Matrix.PSL3Two.PSL
  space : V ≃ₗ[ZMod 2] Vector
  intertwines : ∀ a v, space (ρ a v) =
    W (Matrix.PSL3Two.equiv.symm (actor a)) (space v)

theorem NaturalModel.not_self_dual {ρ : Representation (ZMod 2) A V}
    (m : NaturalModel ρ) : ¬ Nonempty (Representation.Equiv ρ ρ.dual) :=
  AutomorphismAction.not_self_dual_of_natural_coordinates ρ
    (m.actor.trans Matrix.PSL3Two.equiv.symm) m.space m.intertwines

theorem NaturalModel.finrank_eq_three {ρ : Representation (ZMod 2) A V}
    (m : NaturalModel ρ) : Module.finrank (ZMod 2) V = 3 := by
  rw [m.space.finrank_eq]
  change Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3
  simp
end BinaryLinearThree

namespace BinaryLinearThree
open Representation
variable {A V : Type*} [_root_.Group A] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) A V}

/-- Representation equivalence retaining the actual projective-to-linear transport. -/
def NaturalModel.toEquiv (m : NaturalModel ρ) :
    Representation.Equiv ρ (W.comp (m.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom) where
  toLinearEquiv := m.space
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    exact m.intertwines a v

/-- Dual coordinates use the very same actor isomorphism as the natural coordinates. -/
def NaturalModel.dualEquiv (m : NaturalModel ρ) :
    Representation.Equiv ρ.dual
      (W.dual.comp (m.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom) where
  toLinearEquiv := m.space.symm.dualMap
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change f (ρ a⁻¹ (m.space.symm w)) =
      f (m.space.symm (W (Matrix.PSL3Two.equiv.symm (m.actor a))⁻¹ w))
    congr 1
    apply m.space.injective
    rw [m.intertwines, m.space.apply_symm_apply, m.space.apply_symm_apply,
      map_inv, map_inv]
end BinaryLinearThree
