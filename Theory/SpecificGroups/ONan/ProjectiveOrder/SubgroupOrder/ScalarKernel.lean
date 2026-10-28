module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearSetup

/-!
# Scalar kernel of the O'Nan local lifts

The two local lifts preserve a bilinear form with a nonzero diagonal entry and
have determinant one. A scalar in their subgroup therefore has square one by
the form and 45th power one by its determinant, hence is the identity.

The concrete form and determinant checks are separate certificates for the
ATLAS matrices and local words in `ProjectiveOrder/source/README.md`.
-/

namespace ONan.OrderCertificate

set_option maxRecDepth 1024

private abbrev Linear := Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)
private abbrev Form := Matrix (Fin 45) (Fin 45) (ZMod 7)

/-- Isometries of a possibly degenerate bilinear form. -/
private def formStabilizer (F : Form) : Subgroup Linear where
  carrier := {g | g.val.transpose * F * g.val = F}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change (g.val * h.val).transpose * F * (g.val * h.val) = F
    calc
      _ = h.val.transpose * (g.val.transpose * F * g.val) * h.val := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = F := by rw [hg, hh]
  inv_mem' {g} hg := by
    change (g⁻¹).val.transpose * F * (g⁻¹).val = F
    have hcancel : g.val * (g⁻¹).val = 1 := by
      have h := congrArg (fun x : Linear => x.val) (mul_inv_cancel g)
      simpa only [Units.val_mul, Units.val_one] using h
    calc
      _ = (g⁻¹).val.transpose * (g.val.transpose * F * g.val) * (g⁻¹).val := by rw [hg]
      _ = (g.val * (g⁻¹).val).transpose * F * (g.val * (g⁻¹).val) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = F := by rw [hcancel]; simp

private theorem local_preserves_form (F : Form)
    (hA : linearLocalA.val.transpose * F * linearLocalA.val = F)
    (hB : linearLocalB.val.transpose * F * linearLocalB.val = F) :
    linearLocalSubgroup ≤ formStabilizer F := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact hA
  · exact hB

private theorem local_det_one
    (hA : linearLocalA.det = 1) (hB : linearLocalB.det = 1) :
    linearLocalSubgroup ≤ Matrix.GeneralLinearGroup.det.ker := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact hA
  · exact hB

/-- A scalar preserving a form with a unit diagonal entry and having determinant one is one. -/
public theorem scalar_eq_one_of_form_and_det
    (F : Matrix (Fin 45) (Fin 45) (ZMod 7)) (hF : F 0 0 = 1)
    (u : (ZMod 7)ˣ)
    (hform : (Matrix.scalar (Fin 45) u.val).transpose * F *
      Matrix.scalar (Fin 45) u.val = F)
    (hdet : u ^ 45 = 1) : u = 1 := by
  have hsq : u ^ 2 = 1 := by
    apply Units.ext
    have hentry := congrArg (fun M : Form => M 0 0) hform
    simp only [Matrix.scalar_apply, Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hF, mul_one] at hentry
    simpa only [pow_two, Units.val_mul, Units.val_one] using hentry
  have hodd : u ^ 45 = u := by
    calc
      u ^ 45 = (u ^ 2) ^ 22 * u := by group
      _ = u := by rw [hsq]; simp
  exact hodd.symm.trans hdet

/-- The local scalar kernel is trivial once the two concrete matrix checks are supplied. -/
public theorem linearLocal_scalar_eq_one_of_certificates
    (F : Matrix (Fin 45) (Fin 45) (ZMod 7)) (hF : F 0 0 = 1)
    (hAform : linearLocalA.val.transpose * F * linearLocalA.val = F)
    (hBform : linearLocalB.val.transpose * F * linearLocalB.val = F)
    (hAdet : linearLocalA.det = 1)
    (hBdet : linearLocalB.det = 1)
    (u : (ZMod 7)ˣ)
    (hu : Matrix.GeneralLinearGroup.scalar (Fin 45) u ∈ linearLocalSubgroup) :
    u = 1 := by
  have hform0 := local_preserves_form F hAform hBform hu
  change (Matrix.GeneralLinearGroup.scalar (Fin 45) u).val.transpose * F *
    (Matrix.GeneralLinearGroup.scalar (Fin 45) u).val = F at hform0
  have hform : (Matrix.scalar (Fin 45) u.val).transpose * F *
      Matrix.scalar (Fin 45) u.val = F := by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar] using hform0
  have hdet : u ^ 45 = 1 := by
    have h := local_det_one hAdet hBdet hu
    change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 45) u) = 1 at h
    rw [Matrix.GeneralLinearGroup.det_scalar] at h
    simpa only [Fintype.card_fin] using h
  exact scalar_eq_one_of_form_and_det F hF u hform hdet

end ONan.OrderCertificate
