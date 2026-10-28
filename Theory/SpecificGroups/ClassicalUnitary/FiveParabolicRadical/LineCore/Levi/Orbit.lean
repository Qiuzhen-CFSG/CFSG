module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Levi.Structure
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Transporting the natural SU₃ isotropic-line orbit

Huppert II.10.12 constructs the natural projective action on the 65 isotropic
points at parameter four and proves its transitivity. A matrix conjugation
identifying two special unitary groups carries the standard first-coordinate
line stabilizer to the stabilizer of the first column of the basis matrix.
Surjectivity of SU₃ → PSU₃ and orbit--stabilizer give index 65. The natural
matrix action formula is used explicitly in identifying the stabilizers.

Source: Huppert, *Endliche Gruppen I*, II.10.12; the overlap calculation for
Aschbacher--Smith F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization Pointwise
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Levi
variable {F : Type*} [Field F]

noncomputable def matrixLinear : GL (Fin 3) F →* ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

noncomputable def linearAction (J : HermitianForm 3 F) :
    J.specialSubgroup →* ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :=
  matrixLinear.comp J.specialSubgroup.subtype

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
/-- A natural matrix equivalence transports the standard isotropic-line stabilizer. -/
theorem lineStabilizer_index_of_transport [Finite F]
    (J J₀ : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hfixed : Nat.card {x : F // J₀.conj x = x} = 4)
    (hstandard : J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (C : GL (Fin 3) F) (e : J.specialSubgroup ≃* J₀.specialSubgroup)
    (he : ∀ A, (e A : GL (Fin 3) F) = C⁻¹ * A * C) :
    ((MulAction.stabilizer ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
      (Submodule.span F {C.val *ᵥ ![1, 0, 0]})).comap (linearAction J)).index = 65 := by
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
  have hS : S.index = 65 := by
    change (MulAction.stabilizer G p).index = 65
    rw [MulAction.index_stabilizer_of_transitive]
    omega
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
  rw [hsub, S.index_comap_of_surjective hπ, hS]
end Theory.SpecificGroups.UnitaryFive.LineCore.Levi
