module
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover.FullTorusFixer
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Detecting the graph action from a fixed projective Borel

A special-linear automorphism that moves the scalar center and fixes the
whole projective Borel torus has no field contribution. Standard
linear-field-graph factorization and the two torus axes eliminate the
linear-only branch, force field order four and leave an explicit GL₃
conjugation followed by inverse transpose. The original projective action
is retained; merely being outer would not suffice.

Source: Aschbacher–Smith 14.7.41 and 14.7.44, printed pp.1061–1062,
refs/quasithin.pdf. The matrix calculations reuse the attributed ATLAS
ports in the imported modules (LICENSES/ATLAS.txt).
-/

public section
open scoped MatrixGroups
open Subgroup
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions
namespace Matrix.SL3.BorelGraph
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A central-moving automorphism fixing the projective Borel torus has a pure
linear-graph factorization, and its coefficient field has order four. -/
theorem graph_of_projective_borel_fixed {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (α : MulAut SL(3,F))
    (hU : (unipotent F).map (centerAction F α).toMonoidHom = unipotent F)
    (hfix : ∀ x ∈ torus F, centerAction F α x * x⁻¹ ∈ unipotent F)
    (hmove : ¬ ∀ z ∈ center SL(3,F), α z = z) :
    n = 2 ∧ ∃ m : GL (Fin 3) F, α = linearConjSL F m * graphSL F := by
  let β := centerAction F α
  change (unipotent F).map β.toMonoidHom = unipotent F at hU
  change ∀ x ∈ torus F, β x * x⁻¹ ∈ unipotent F at hfix
  have hs : β ∈ standard F := by
    rw [standard_eq_top_of_two_power_card F (by omega : 0 < n) hF]
    trivial
  obtain ⟨m,σ,he | he⟩ := ResidualLinear.standard_opposition_factorization β hs
  · have ht := ResidualLinear.linear_field_upperTriangular m σ (by rwa [←he])
    have hσ : σ = 1 := by
      ext x
      by_cases hx : x = 0
      · simp [hx]
      · let u := Units.mk0 x hx
        have hp := ResidualLinear.parameters_eq_of_displacement m ht
          (Units.map σ.toMonoidHom u,1) (u,1) (by
            simpa only [he,MulAut.mul_apply,field_torusMap,map_one] using
              hfix (torusMap F (u,1)) ⟨(u,1),rfl⟩)
        exact congrArg Units.val (ResidualParameters.projective_axis_injective hp)
    have ha : α = linearConjSL F m := by
      apply ActorCoverage.centerAction_injective F
      change β = linearConj F m
      simpa only [hσ,map_one,mul_one] using he
    exfalso
    apply hmove
    intro z hz
    rw [ha]
    apply SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL]
    have hc := (SpecialLinearGroup.toGL_mem_center_iff z).mpr hz
    rw [mem_center_iff.mp hc m,mul_inv_cancel_right]
  · have hn2 : n = 2 := by
      by_contra hh
      apply ResidualLinear.linear_graph_field_not_fixed hF hn hh m σ (by rwa [←he])
      intro u _
      simpa only [←he] using hfix (torusMap F (u,1)) ⟨(u,1),rfl⟩
    have hb : (unipotent F).map
        (fieldAction F σ * oppositionGraph F).toMonoidHom = unipotent F := by
      change (unipotent F).map
        ((fieldAction F σ).toMonoidHom.comp (oppositionGraph F).toMonoidHom) = _
      rw [←Subgroup.map_map,oppositionGraph_unipotent,fieldAction_unipotent]
    have hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F := by
      have hu := hU
      rw [he,mul_assoc] at hu
      change (unipotent F).map ((linearConj F m).toMonoidHom.comp
        (fieldAction F σ * oppositionGraph F).toMonoidHom) = _ at hu
      rwa [←Subgroup.map_map,hb] at hu
    have ht := NormalizerForm.linearConj_upperTriangular F m hm
    have hσ : σ = 1 := by
      have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
        have hp := ResidualLinear.parameters_eq_of_displacement m ht
          (1,(Units.map σ.toMonoidHom u)⁻¹) (u,1) (by
            simpa only [he,MulAut.mul_apply,oppositionGraph_torusMap,
              field_torusMap,inv_one,map_one,map_inv] using
              hfix (torusMap F (u,1)) ⟨(u,1),rfl⟩)
        have hh := (ResidualParameters.projective_parameters_eq_iff _ _).mp hp
        have hi : u⁻¹ = (Units.map σ.toMonoidHom u)⁻¹ := by simpa using hh.1
        exact inv_injective hi.symm
      ext x
      by_cases hx : x = 0
      · simp [hx]
      · exact congrArg Units.val (hu (Units.mk0 x hx))
    refine ⟨hn2,m * reversalGL F,ActorCoverage.centerAction_injective F ?_⟩
    rw [map_mul]
    change β = linearConj F (m * reversalGL F) * graph F
    rw [he,hσ,map_one,mul_one]
    change linearConj F m * (linearConj F (reversalGL F) * graph F) = _
    rw [←mul_assoc,←map_mul]
end Matrix.SL3.BorelGraph
