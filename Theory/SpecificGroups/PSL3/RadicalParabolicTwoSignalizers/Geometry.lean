module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Parabolic radicals over the five-element field

The scalar kernel of SL₃(5) → PSL₃(5) is trivial. Thus the valid
SL₃ root-plane normalizer calculation passes to PSL₃ without using any
characteristic-two theorem. Both coordinate radicals are elementary abelian
of order 25. The model is centerless, as also follows directly from its
faithful central quotient projection.

`IsParabolicRadical` records conjugacy of an actual marked subgroup. Recognition
of arbitrary elementary kernels in subgroups with quotient SL₂(5) is a separate
obligation; none of the results below assumes or asserts that recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed p.513. The matrix carriers and coordinate equivalences
are those of the attributed imports; no new ATLAS source is copied here.
-/

@[expose] public section

open scoped MatrixGroups IsMulCommutative
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.RadicalParabolicTwoSignalizers

instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual projective special linear group over the five-element field. -/
abbrev Model := PSL(3, ZMod 5)

local notation "F" => ZMod 5
local notation "L" => Model

theorem projection_injective : Function.Injective (projection F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Subgroup.eq_bot_of_card_eq
  rw [card_projectionKernel, Nat.card_zmod]
  decide

noncomputable def projectionEquiv : SL(3,F) ≃* L :=
  MulEquiv.ofBijective (projection F) ⟨projection_injective, projection_surjective F⟩

theorem center_eq_bot : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := projection_surjective F y
  have hx : x ∈ center SL(3,F) := by
    rw [mem_center_iff]
    intro z
    apply projection_injective
    simpa only [map_mul] using (mem_center_iff.mp hy) (projection F z)
  exact mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)

theorem normalizer_rootPlane_five (point : Bool) :
    normalizer (rootPlane F point) = parabolic F point := by
  rw [rootPlane, ← (rootPlaneSL F point).map_normalizer_eq_of_bijective
      ⟨projection_injective, projection_surjective F⟩,
    normalizer_rootPlaneSL]
  exact (parabolic_eq_map F point).symm

theorem rootPlane_eq_map (point : Bool) :
    rootPlane F point = (if point then V₁ F else V₂ F).map (projective F) := by
  rw [rootPlane, rootPlaneSL, Subgroup.map_map]
  rfl

theorem card_rootPlane (point : Bool) : Nat.card (rootPlane F point) = 25 := by
  rw [rootPlane_eq_map, card_map_of_injective (projective_injective F)]
  cases point <;> simp only [Bool.false_eq_true, ↓reduceIte, card_V₂, card_V₁, Nat.card_zmod]
  all_goals decide

private theorem elementary_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) [IsElementaryAbelian 5 A] : IsElementaryAbelian 5 B where
  toIsMulCommutative := ⟨⟨fun a b => e.symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun b => by
    apply e.symm.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 5 A) (e.symm b)))

theorem rootPlane_elementary (point : Bool) : IsElementaryAbelian 5 (rootPlane F point) := by
  let : IsElementaryAbelian 5 (Multiplicative (F × F)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      change 5 • a.toAdd = 0
      exact ZModModule.char_nsmul_eq_zero 5 a.toAdd) }
  rw [rootPlane_eq_map]
  cases point
  · change IsElementaryAbelian 5 ((V₂ F).map (projective F))
    let : IsElementaryAbelian 5 (V₂ F) := elementary_of_equiv (plane₂Equiv F)
    exact IsElementaryAbelian.map (projective F)
  · change IsElementaryAbelian 5 ((V₁ F).map (projective F))
    let : IsElementaryAbelian 5 (V₁ F) := elementary_of_equiv (plane₁Equiv F)
    exact IsElementaryAbelian.map (projective F)

/-- Conjugacy to one of the two actual coordinate parabolic radicals.
The equality retains the specified subgroup, including its embedding. -/
def IsParabolicRadical (P : Subgroup Model) : Prop :=
  ∃ point : Bool, ∃ g : Model,
    (rootPlane F point).map (MulAut.conj g).toMonoidHom = P

end Matrix.PSL3.RadicalParabolicTwoSignalizers
