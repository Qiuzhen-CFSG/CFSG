module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Orbit
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximality of the transported isotropic-line stabilizer

The natural SU₃ action on its isotropic lines is two-transitive. A supplied
matrix conjugation transports its point stabilizer to the stabilizer of the
first column of that matrix. Two-transitivity and surjective pullback make
this subgroup maximal; all projective actions use the actual scalar quotient.

Source: Huppert, II.10.12; Aschbacher--Smith F.1.3 and F.1.12(7), printed
pp.260 and 263--264. This extends the marked index calculation in
`LineCore.Levi.Orbit` without changing its public interface.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization Pointwise
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Levi.Borel
open LineCore.Levi
variable {F : Type*} [Field F]
private theorem submodule_smul (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (p : ℙ F (Fin 3 → F)) : (e • p).submodule = e • p.submodule := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.smul_mk, Projectivization.submodule_mk,
      Projectivization.submodule_mk]
    change Submodule.span F {e v} = (Submodule.span F {v}).map e.toLinearMap
    rw [Submodule.map_span, Set.image_singleton]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Two-transitivity makes the transported isotropic-line stabilizer maximal. -/
theorem lineStabilizer_isCoatom_of_transport [Finite F]
    (J J₀ : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hfixed : Nat.card {x : F // J₀.conj x = x} = 4)
    (hstandard : J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (C : GL (Fin 3) F) (e : J.specialSubgroup ≃* J₀.specialSubgroup)
    (he : ∀ A, (e A : GL (Fin 3) F) = C⁻¹ * A * C) :
    IsCoatom ((MulAction.stabilizer ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
      (Submodule.span F {C.val *ᵥ ![1, 0, 0]})).comap (linearAction J)) := by
  classical
  let P := ℙ F (Fin 3 → F)
  let Ω := {x : P // ∃ (v : Fin 3 → F) (hv : v ≠ 0),
    x = Projectivization.mk F v hv ∧
      dotProduct (fun i => J₀.conj (v i)) (J₀.form.mulVec v) = 0}
  obtain ⟨hΩ, rho, _, _, hrho, _, _, htwo, _, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J₀ 4 hcard hfixed hstandard
  change Nat.card Ω = 4 ^ 3 + 1 at hΩ
  let G := ProjectiveSpecialUnitaryMatrixGroup J₀
  change G →* Equiv.Perm Ω at rho
  let : MulAction G Ω := MulAction.compHom Ω rho
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega : 1 < Nat.card Ω)
  let : MulAction.IsPretransitive G Ω := ⟨fun a b => by
    obtain ⟨a', ha'⟩ := exists_ne a
    obtain ⟨b', hb'⟩ := exists_ne b
    obtain ⟨g, hg, _⟩ := htwo a a' b b' (Ne.symm ha') (Ne.symm hb')
    exact ⟨g, hg⟩⟩
  have hv : (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  let p : Ω := ⟨Projectivization.mk F ![1, 0, 0] hv,
    ![1, 0, 0], hv, rfl, by
      simp [hstandard, Matrix.mulVec, dotProduct, Fin.sum_univ_three]⟩
  let S := (MulAction.stabilizer (Equiv.Perm Ω) p).comap rho
  have : MulAction.IsMultiplyPretransitive G Ω 2 :=
    MulAction.is_two_pretransitive_iff.mpr (fun {a b c d} hab hcd => by
      obtain ⟨g,hg,hg'⟩ := htwo a b c d hab hcd
      exact ⟨g,hg,hg'⟩)
  have : MulAction.IsPreprimitive G Ω := MulAction.isPreprimitive_of_is_two_pretransitive inferInstance
  have hS : IsCoatom S := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G p
  let π : J.specialSubgroup →* G := (project J₀).comp e.toMonoidHom
  have hπ : Function.Surjective π := (project_surjective J₀).comp e.surjective
  have hlinear (A : J.specialSubgroup) :
      matrixLinear C * linearAction J₀ (e A) = linearAction J A * matrixLinear C := by
    change matrixLinear C * matrixLinear (e A : GL (Fin 3) F) =
      matrixLinear (A : GL (Fin 3) F) * matrixLinear C
    rw [← map_mul, ← map_mul, he]
    congr 1
    group
  have hact (A : J.specialSubgroup) :
      matrixLinear C • ((rho (π A) p : Ω) : P) =
        linearAction J A • (matrixLinear C • (p : P)) := by
    have hr := hrho (π A) p (e A) rfl
    change ((rho (π A) p : Ω) : P) = linearAction J₀ (e A) • (p : P) at hr
    rw [hr]
    rw [← mul_smul, hlinear, mul_smul]
  have hp : (matrixLinear C • (p : P)).submodule =
      Submodule.span F {C.val *ᵥ ![1, 0, 0]} := by
    rw [show (p : P) = Projectivization.mk F ![1, 0, 0] hv from rfl,
      Projectivization.smul_mk, Projectivization.submodule_mk]
    rfl
  have hsub :
      (MulAction.stabilizer ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
        (Submodule.span F {C.val *ᵥ ![1, 0, 0]})).comap (linearAction J) = S.comap π := by
    ext A
    change linearAction J A • Submodule.span F {C.val *ᵥ ![1, 0, 0]} =
        Submodule.span F {C.val *ᵥ ![1, 0, 0]} ↔ rho (π A) p = p
    rw [← hp, ← submodule_smul, ← hact]
    rw [Projectivization.submodule_injective.eq_iff, smul_left_cancel_iff]
    exact Subtype.val_injective.eq_iff
  rw [hsub]
  exact Subgroup.isCoatom_comap_of_surjective hπ hS
end Theory.SpecificGroups.UnitaryFive.LineCore.Levi.Borel
