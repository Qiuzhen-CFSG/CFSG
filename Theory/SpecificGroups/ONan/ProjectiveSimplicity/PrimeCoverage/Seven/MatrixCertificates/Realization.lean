module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.MatrixCertificates.Values
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Collection

/-!
# Linear realization of the seven-coordinate generators

Balanced products certify the fixed words against the ATLAS matrices. The
seventh powers and collection equations then follow from the checked matrix
tables, before passing to the projective quotient. Sources and matrix
attribution are in `refs/original/onan/` and `ProjectiveOrder/Setup.lean`.
-/

namespace ONan.Simplicity.Seven
open Certificate ONan.OrderCertificate

@[expose] public def linearX : Certificate.LinearGroup := lift_m27
@[expose] public def linearAuxiliaryY : Certificate.LinearGroup := lift_m41
@[expose] public def linearY : Certificate.LinearGroup := lift_m51
@[expose] public def linearZ : Certificate.LinearGroup := lift_z

private theorem lift_la_eq : lift_la = linearLocalA := rfl
private theorem lift_lb_eq : lift_lb = linearLocalB := by
  simp only [lift_lb, lift_m6, lift_ci, lift_c, lift_ab2, lift_bb,
    lift_a, lift_b, linearLocalB, pow_two]

public theorem project_linearX :
    Matrix.ProjGenLinGroup.mk linearX = (generatorX).val := by
  change Matrix.ProjGenLinGroup.mk linearX = modelInclusion generatorX
  simp only [linearX, generatorX, lift_m9, lift_m10, lift_m11, lift_m12, lift_m13, lift_m14,
    lift_m15, lift_m16, lift_m17, lift_m18, lift_m19, lift_m20,
    lift_m21, lift_m22, lift_m23, lift_m24, lift_m25, lift_m26,
    lift_m27, lift_lbi,
    lift_la_eq, lift_lb_eq, map_mul, map_inv, mk_linearLocalA, mk_linearLocalB,
    modelInclusion, mul_assoc]
  rfl

public theorem project_linearAuxiliaryY :
    Matrix.ProjGenLinGroup.mk linearAuxiliaryY = (auxiliaryY).val := by
  change Matrix.ProjGenLinGroup.mk linearAuxiliaryY = modelInclusion auxiliaryY
  simp only [linearAuxiliaryY, auxiliaryY, lift_m9, lift_m13, lift_m18, lift_m19, lift_m22, lift_m23,
    lift_m28, lift_m29, lift_m30, lift_m31, lift_m32, lift_m33,
    lift_m34, lift_m35, lift_m36, lift_m37, lift_m38, lift_m39,
    lift_m40, lift_m41, lift_lbi,
    lift_la_eq, lift_lb_eq, map_mul, map_inv, mk_linearLocalA, mk_linearLocalB,
    modelInclusion, mul_assoc]
  rfl

public theorem project_linearY :
    Matrix.ProjGenLinGroup.mk linearY = (generatorY).val := by
  change Matrix.ProjGenLinGroup.mk linearY = modelInclusion generatorY
  simp only [linearY, generatorY, lift_m13, lift_m18, lift_m19, lift_m22, lift_m23, lift_m29,
    lift_m30, lift_m37, lift_m42, lift_m43, lift_m44, lift_m45,
    lift_m46, lift_m47, lift_m48, lift_m49, lift_m50, lift_m51, lift_lbi,
    lift_la_eq, lift_lb_eq, map_mul, map_inv, mk_linearLocalA, mk_linearLocalB,
    modelInclusion, mul_assoc]
  rfl

public theorem linearZ_eq : linearZ = linearAuxiliaryY * linearY⁻¹ := rfl

public theorem project_linearZ :
    Matrix.ProjGenLinGroup.mk linearZ = generatorZ.val := by
  rw [linearZ_eq, map_mul, map_inv, project_linearAuxiliaryY, project_linearY]
  rfl

public theorem linearX_matrix : (linearX : Mat) = m27 := value_m27
public theorem linearAuxiliaryY_matrix : (linearAuxiliaryY : Mat) = m41 := value_m41
public theorem linearY_matrix : (linearY : Mat) = m51 := value_m51
public theorem linearZ_matrix : (linearZ : Mat) = z := value_z

public theorem linearX_pow_seven : linearX ^ 7 = 1 := by
  have h : lift_x7 = 1 := by
    apply Units.ext
    exact value_x7.trans encoded_one_eq
  calc
    linearX ^ 7 = lift_x7 := by
      simp only [linearX, lift_x7, lift_x6, lift_x4, lift_x2,
        pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h

public theorem linearY_pow_seven : linearY ^ 7 = 1 := by
  have h : lift_y7 = 1 := by
    apply Units.ext
    exact value_y7.trans encoded_one_eq
  calc
    linearY ^ 7 = lift_y7 := by
      simp only [linearY, lift_y7, lift_y6, lift_y4, lift_y2,
        pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h

public theorem linearZ_pow_seven : linearZ ^ 7 = 1 := by
  have h : lift_z7 = 1 := by
    apply Units.ext
    exact value_z7.trans encoded_one_eq
  calc
    linearZ ^ 7 = lift_z7 := by
      simp only [linearZ, lift_z7, lift_z6, lift_z4, lift_z2,
        pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h

public theorem linearZ_commute_linearX : Commute linearZ linearX := by
  show linearZ * linearX = linearX * linearZ
  apply Units.ext
  exact value_zx.trans value_xz.symm

public theorem linearZ_commute_linearY : Commute linearZ linearY := by
  show linearZ * linearY = linearY * linearZ
  apply Units.ext
  exact value_zy.trans value_yz.symm

public theorem linear_collection : linearY * linearX = linearZ * linearX * linearY := by
  apply Units.ext
  exact value_yx.trans value_zxy.symm

end ONan.Simplicity.Seven
