module
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Sylow omega-center orders in binary SL₂ quotients

A defining-characteristic Sylow of SL₂(F) is the additive field. In
characteristic two it is elementary abelian, so its central first omega
is the whole Sylow. Transport through a supplied quotient marking
therefore computes the omega-center order as |F|, independently of the
chosen Sylow.

Source application: the parameter q in DGS, Groups and Graphs (1985),
6.0 and 6.4(c), pp.118,120. The source consumer retains its actual quotient.
-/

open Subgroup
open scoped MatrixGroups
public noncomputable section
namespace Matrix.SpecialLinearGroup
variable {D F : Type*} [Group D] [Field F] [Finite F] [CharP F 2]

/-- An actual binary SL₂ marking determines the omega-center order of every Sylow. -/
theorem card_omegaCenter_sylow_of_equiv
    (e : D ≃* SL(2,F)) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) = Nat.card F := by
  let : Finite D := Finite.of_equiv SL(2,F) e.symm.toEquiv
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : T ≃* Multiplicative F :=
    ((T : Subgroup D).equivMapOfInjective e.toMonoidHom e.injective).trans
      (sylowEquivAdditive F 2 U).symm
  have hc : omegaCenterIn (T : Subgroup D) = T := by
    apply le_antisymm (map_subtype_le _) ?_
    intro x hx
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨hx,?_,?_⟩
    · intro y hy
      have he : (⟨y,hy⟩ : T) * ⟨x,hx⟩ = ⟨x,hx⟩ * ⟨y,hy⟩ := a.injective (by
        simp only [map_mul]
        exact mul_comm (a ⟨y,hy⟩) (a ⟨x,hx⟩))
      exact congrArg Subtype.val he
    · have hp : (⟨x,hx⟩ : T)^2 = 1 := by
        apply a.injective
        rw [map_pow,map_one]
        change (2 : ℕ) • (a ⟨x,hx⟩).toAdd = 0
        simp only [nsmul_eq_mul,CharP.cast_eq_zero F 2,zero_mul]
      exact congrArg Subtype.val hp
  rw [hc]
  exact Nat.card_congr a.toEquiv
end Matrix.SpecialLinearGroup
