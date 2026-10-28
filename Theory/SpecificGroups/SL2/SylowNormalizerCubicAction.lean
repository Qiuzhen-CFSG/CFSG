module
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.FieldTheory.CubicDisplacement
/-!
# Cubic displacement on a binary Sylow-normalizer quotient

Transport the specified group and automorphism to SL₂ over the given
field. The marked Sylow-normalizer character intertwines the action with
a field automorphism and has exactly the specified Sylow as kernel.
Cubic displacement forces that field automorphism to fix all cubes.
Above field order four it is trivial, so every displacement belongs to
the same Sylow subgroup.

Source application: Aschbacher--Smith 12.6.31, printed pp.836--837,
refs/quasithin.pdf. No invariant Hall complement is selected.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {Q F : Type*} [Group Q] [Finite Q] [Field F] [Finite F] [CharP F 2]

theorem sylowNormalizer_displacement_mem_of_cube
    (e : Q ≃* SL(2,F)) (S : Sylow 2 Q) (α : MulAut Q)
    (hS : (S : Subgroup Q).map α.toMonoidHom = S)
    (hF : 4 < Nat.card F)
    (hc : ∀ x ∈ normalizer (S : Set Q), (α x * x⁻¹)^3 ∈ (S : Subgroup Q)) :
    ∀ x ∈ normalizer (S : Set Q), α x * x⁻¹ ∈ (S : Subgroup Q) := by
  let β := MulAut.congr e α
  obtain ⟨f,σ,hf,hk,he⟩ := exists_sylowNormalizer_torus_action e.toMonoidHom e.surjective S
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le) α β
    (fun x => by simp [β,MulAut.congr_apply]) hS
  have hn : (normalizer (S : Set Q)).map α.toMonoidHom = normalizer (S : Set Q) := by
    simpa only [hS,Sylow.coe_coe] using
      map_normalizer_eq_of_bijective (f := α.toMonoidHom) (S : Subgroup Q) α.bijective
  let a : MulAut (normalizer (S : Set Q)) :=
    (α.subgroupMap _).trans (MulEquiv.subgroupCongr hn)
  have hσ : ∀ u : Fˣ, (Units.map σ.toMonoidHom u * u⁻¹)^3 = 1 := by
    intro u
    obtain ⟨x,rfl⟩ := hf u
    rw [←he x (a x) rfl,←map_inv,←map_mul,←map_pow]
    exact (hk _).mpr (hc x x.property)
  have hσ1 : σ = 1 :=
    (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ hσ).resolve_right
      (Nat.not_le_of_gt hF)
  intro x hx
  let y : normalizer (S : Set Q) := ⟨x,hx⟩
  apply (hk (a y * y⁻¹)).mp
  rw [map_mul,map_inv,he y (a y) rfl,hσ1]
  change f y * (f y)⁻¹ = 1
  exact mul_inv_cancel _
end Matrix.SpecialLinearGroup
