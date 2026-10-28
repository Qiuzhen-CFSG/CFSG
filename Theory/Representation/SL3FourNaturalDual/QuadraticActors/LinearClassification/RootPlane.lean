module

public import Theory.Representation.SL3FourNaturalDual.Markings

/-!
# Binary subgroups of the literal SL₃(4) root plane

The two parameters occupy matrix entries (0,1) and (0,2). Their additive
law gives a quadratic matrix subgroup for every binary parameter subspace,
and the explicit parameter bijection identifies its rank with that
subspace's binary dimension. The displacement formula keeps both summands
of the natural-plus-dual representation.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open Matrix BinaryOffender

/-- The root plane with common image the first coordinate line. -/
def plane (p : F × F) : SL :=
  ⟨!![1, p.1, p.2; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

lemma plane_zero : plane 0 = 1 := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [plane]

lemma plane_add (p q : F × F) : plane (p + q) = plane p * plane q := by
  apply Subtype.ext
  change (plane (p + q)).val = (plane p).val * (plane q).val
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [plane, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

lemma plane_inv (p : F × F) : (plane p)⁻¹ = plane p := by
  apply inv_eq_of_mul_eq_one_left
  rw [← plane_add, CharTwo.add_self_eq_zero, plane_zero]

lemma plane_injective : Function.Injective plane := by
  intro p q h
  exact Prod.ext (congrArg (fun g : SL => g 0 1) h)
    (congrArg (fun g : SL => g 0 2) h)

lemma plane_root (a : F) : plane (0, a) = root a := rfl
lemma plane_secondRoot (a : F) : plane (a, 0) = secondRoot a := rfl

lemma plane_displacement (p : F × F) (v : V) :
    representation (plane p) v - v =
      (![p.1 * v.1 1 + p.2 * v.1 2, 0, 0], ![0, p.1 * v.2 0, p.2 * v.2 0]) := by
  rw [representation_apply, plane_inv]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [plane, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_sub_cancel_left,
      add_assoc]

/-- The subgroup with a specified binary parameter space. -/
def planeActor (D : Submodule (ZMod 2) (F × F)) : Subgroup SL where
  carrier := {g | ∃ p ∈ D, plane p = g}
  one_mem' := ⟨0, D.zero_mem, plane_zero⟩
  mul_mem' := by
    rintro g h ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p+q, D.add_mem hp hq, plane_add p q⟩
  inv_mem' := by
    rintro g ⟨p, hp, rfl⟩
    exact ⟨p, hp, (plane_inv p).symm⟩

lemma mem_planeActor (D : Submodule (ZMod 2) (F × F)) (p : F × F) :
    plane p ∈ planeActor D ↔ p ∈ D := by
  constructor
  · rintro ⟨q, hq, h⟩
    exact plane_injective h ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Parameterization also identifies the finite carrier, so rank is literal
binary dimension. -/
def planeActorEquiv (D : Submodule (ZMod 2) (F × F)) : D ≃ planeActor D :=
  Equiv.ofBijective (fun p => ⟨plane p, (mem_planeActor D p).mpr p.property⟩) (by
    constructor
    · intro p q h
      exact Subtype.ext (plane_injective (congrArg Subtype.val h))
    · rintro ⟨g, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩)

lemma planeActor_rank (D : Submodule (ZMod 2) (F × F)) :
    BinaryOffender.rank (planeActor D) = Module.finrank (ZMod 2) D := by
  unfold BinaryOffender.rank
  rw [← Nat.card_congr (planeActorEquiv D), Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card, Nat.log_pow (by decide : 1 < 2)]

lemma planeActor_ne_bot (D : Submodule (ZMod 2) (F × F)) :
    planeActor D ≠ ⊥ ↔ D ≠ ⊥ := by
  constructor
  · intro h hD
    apply h
    ext g
    change (∃ p ∈ D, plane p = g) ↔ g = 1
    simp [hD, plane_zero, eq_comm]
  · intro h hA
    apply h
    apply le_bot_iff.mp
    intro p hp
    have hg : plane p ∈ (⊥ : Subgroup SL) := hA ▸ (mem_planeActor D p).mpr hp
    exact plane_injective (hg.trans plane_zero.symm)

lemma planeActor_quadratic (D : Submodule (ZMod 2) (F × F)) :
    IsQuadratic representation (planeActor D) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ v
  apply sub_eq_zero.mp
  rw [plane_displacement, plane_displacement]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
