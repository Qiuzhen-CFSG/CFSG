module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.MatrixCertificates.Realization

/-!
# Certified seven-coordinate realization in the O'Nan model

The six linear relations descend to the fixed projective words and give the
coordinate multiplication law. Entry (0,15) distinguishes XY from every scalar
multiple of YX, proving projective noncommutation. Together these results feed
`coordinateHom_range_card`, with no order, simplicity, or recognition premise.
Sources: the ATLAS matrices in `refs/original/onan/` and the word attribution
in `ProjectiveOrder/Setup.lean`.
-/

namespace ONan.Simplicity.Seven
open Certificate

private theorem val_mul (g h : Model) : (g * h).val = g.val * h.val := rfl
private theorem val_one : (1 : Model).val = 1 := rfl
private theorem val_pow (g : Model) (n : ℕ) : (g ^ n).val = g.val ^ n :=
  ONan.OrderCertificate.modelInclusion.map_pow g n


public theorem generatorX_pow_seven : generatorX ^ 7 = 1 := by
  apply Subtype.ext
  simpa only [val_pow, val_one, map_pow, map_one, project_linearX] using
    congrArg Matrix.ProjGenLinGroup.mk linearX_pow_seven

public theorem generatorY_pow_seven : generatorY ^ 7 = 1 := by
  apply Subtype.ext
  simpa only [val_pow, val_one, map_pow, map_one, project_linearY] using
    congrArg Matrix.ProjGenLinGroup.mk linearY_pow_seven

public theorem generatorZ_pow_seven : generatorZ ^ 7 = 1 := by
  apply Subtype.ext
  simpa only [val_pow, val_one, map_pow, map_one, project_linearZ] using
    congrArg Matrix.ProjGenLinGroup.mk linearZ_pow_seven

public theorem generatorZ_commute_generatorX : Commute generatorZ generatorX := by
  apply Subtype.ext
  simpa only [val_mul, map_mul, project_linearZ, project_linearX] using
    congrArg Matrix.ProjGenLinGroup.mk linearZ_commute_linearX.eq

public theorem generatorZ_commute_generatorY : Commute generatorZ generatorY := by
  apply Subtype.ext
  simpa only [val_mul, map_mul, project_linearZ, project_linearY] using
    congrArg Matrix.ProjGenLinGroup.mk linearZ_commute_linearY.eq

public theorem generator_collection :
    generatorY * generatorX = generatorZ * generatorX * generatorY := by
  apply Subtype.ext
  simpa only [val_mul, map_mul, project_linearX, project_linearY, project_linearZ] using
    congrArg Matrix.ProjGenLinGroup.mk linear_collection

/-- The fixed coordinate evaluation preserves multiplication in the actual model. -/
public theorem evaluate_mul (s t : Coordinates) :
    evaluate (s * t) = evaluate s * evaluate t :=
  evaluate_mul_of_relations generatorX_pow_seven generatorY_pow_seven
    generatorZ_pow_seven generatorZ_commute_generatorX generatorZ_commute_generatorY
    generator_collection s t

/-- The two fixed generators remain noncommuting after projectivization. -/
public theorem generators_noncommute : generatorX * generatorY ≠ generatorY * generatorX := by
  intro h
  have hp : Matrix.ProjGenLinGroup.mk (linearX * linearY) =
      Matrix.ProjGenLinGroup.mk (linearY * linearX) := by
    simpa only [val_mul, map_mul, project_linearX, project_linearY] using congrArg Subtype.val h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have he := congrArg (fun g : LinearGroup => (g : Mat) 0 15) hu
  change (((linearX * linearY : LinearGroup) : Mat) * Matrix.scalar (Fin 45) u.val) 0 15 =
    ((linearY * linearX : LinearGroup) : Mat) 0 15 at he
  change ((lift_xy : Mat) * Matrix.scalar (Fin 45) u.val) 0 15 =
    (lift_yx : Mat) 0 15 at he
  rw [value_xy, value_yx, Matrix.scalar_apply, Matrix.mul_diagonal] at he
  have hxy : xy 0 15 = 0 := by decide +kernel
  have hyx : yx 0 15 = 1 := by decide +kernel
  rw [hxy, hyx, zero_mul] at he
  exact (by decide +kernel : (0 : ZMod 7) ≠ 1) he

end ONan.Simplicity.Seven
