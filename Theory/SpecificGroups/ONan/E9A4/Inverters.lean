module
public import Theory.SpecificGroups.ONan.E9A4.Inverters.Certificates

/-!
# Two actual normalizer words in the O'Nan quotient

The words are evaluated in the fixed ATLAS max5 generators. Exact linear
matrix certificates prove partial inversion of the first E₉ coordinate and
inversion of the A₄ three-cycle. Projectivization removes a verified scalar
four; every element remains a word in the literal O'Nan model generators.
Source: the local E₉ × A₄ argument in Aschbacher–Smith A.2.19, printed p.41.
-/
namespace ONan.E9A4.Inverters

private def wordR {G : Type*} [Group G] (a b : G) : G :=
  let c := localGenerators a b
  ((c 0 * c 0) * (c 1 * (c 0)⁻¹)) * (((c 0)⁻¹ * (c 1)⁻¹) * (c 0 * (c 1)⁻¹))
private def wordS {G : Type*} [Group G] (a b : G) : G :=
  let c := localGenerators a b
  ((c 1 * (c 0)⁻¹) * ((c 1)⁻¹ * (c 0)⁻¹)) *
    (((c 1)⁻¹ * c 0) * (c 1 * (c 0)⁻¹))

private theorem map_local {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 2) :
    f (localGenerators a b i) = localGenerators (f a) (f b) i := by
  fin_cases i <;> simp [localGenerators]
private theorem map_wordR {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (wordR a b) = wordR (f a) (f b) := by
  simp only [wordR, map_mul, map_inv, map_local]
private theorem map_wordS {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (wordS a b) = wordS (f a) (f b) := by
  simp only [wordS, map_mul, map_inv, map_local]

/-- This max5 word inverts the marked A₄ three-cycle. -/
public def cubicInverter : Model := wordR generatorA generatorB
/-- This max5 word inverts the first E₉ cubic and fixes the A₄ three-cycle. -/
public def partialInverter : Model := wordS generatorA generatorB
private def linearR : Linear := wordR linearA linearB
private def linearS : Linear := wordS linearA linearB

private theorem value_linearR : (linearR : Mat) = Certificate.matrixR := by
  change ((WordCertificate.lift_part22 : Mat) * (WordCertificate.lift_part0 : Mat)) *
    ((WordCertificate.lift_part9 : Mat) * (WordCertificate.lift_part34 : Mat)) = _
  rw [WordCertificate.value_part22, WordCertificate.value_part0,
    WordCertificate.value_part9, WordCertificate.value_part34]
  exact Certificate.value_r
private theorem value_linearS : (linearS : Mat) = Certificate.matrixS := by
  change ((WordCertificate.lift_part0 : Mat) * (WordCertificate.lift_part12 : Mat)) *
    ((WordCertificate.lift_part1 : Mat) * (WordCertificate.lift_part0 : Mat)) = _
  rw [WordCertificate.value_part0, WordCertificate.value_part12, WordCertificate.value_part1]
  exact Certificate.value_s
private def inclusion : Model →* Matrix.ProjGenLinGroup (Fin 45) (ZMod 7) :=
  { toFun := fun g => g.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
private theorem project_linearR : Matrix.ProjGenLinGroup.mk linearR = cubicInverter.val := by
  rw [linearR, map_wordR]
  change wordR projectiveA projectiveB = inclusion (wordR generatorA generatorB)
  exact (map_wordR inclusion generatorA generatorB).symm
private theorem project_linearS : Matrix.ProjGenLinGroup.mk linearS = partialInverter.val := by
  rw [linearS, map_wordS]
  change wordS projectiveA projectiveB = inclusion (wordS generatorA generatorB)
  exact (map_wordS inclusion generatorA generatorB).symm

public theorem partial_inverts :
    partialInverter * generators 0 * partialInverter⁻¹ = (generators 0)⁻¹ := by
  let u : (ZMod 7)ˣ := ⟨4, 2, by decide, by decide⟩
  have he : linearGenerators 0 * linearS * linearGenerators 0 =
      Matrix.GeneralLinearGroup.scalar (Fin 45) u * linearS := by
    apply Units.ext
    change (linearGenerators 0 : Mat) * (linearS : Mat) * (linearGenerators 0 : Mat) = _
    change (linearGenerators 0 : Mat) * (linearS : Mat) * (linearGenerators 0 : Mat) =
      Matrix.scalar (Fin 45) (4 : ZMod 7) * (linearS : Mat)
    rw [linearGenerators_matrix, value_linearS]
    change Data.gen0 * Certificate.matrixS * Data.gen0 =
      Matrix.scalar (Fin 45) (4 : ZMod 7) * Certificate.matrixS
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    exact Certificate.matrix_xsx
  have he' : generators 0 * partialInverter * generators 0 = partialInverter := by
    apply Subtype.ext
    change (generators 0).val * partialInverter.val * (generators 0).val = partialInverter.val
    simpa only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
      project_linearGenerators, project_linearS] using congrArg Matrix.ProjGenLinGroup.mk he
  calc
    partialInverter * generators 0 * partialInverter⁻¹ =
      (generators 0)⁻¹ * (generators 0 * partialInverter * generators 0) *
        partialInverter⁻¹ := by group
    _ = (generators 0)⁻¹ := by rw [he']; group

public theorem partial_commutes : Commute partialInverter (generators 3) := by
  have he : linearS * linearGenerators 3 = linearGenerators 3 * linearS := by
    apply Units.ext
    change (linearS : Mat) * (linearGenerators 3 : Mat) =
      (linearGenerators 3 : Mat) * (linearS : Mat)
    rw [value_linearS, linearGenerators_matrix]
    exact Certificate.matrix_st
  apply Subtype.ext
  change partialInverter.val * (generators 3).val = (generators 3).val * partialInverter.val
  simpa only [map_mul, project_linearGenerators, project_linearS] using
    congrArg Matrix.ProjGenLinGroup.mk he

public theorem cubic_inverts :
    cubicInverter * generators 3 * cubicInverter⁻¹ = (generators 3)⁻¹ := by
  have he : linearGenerators 3 * linearR * linearGenerators 3 = linearR := by
    apply Units.ext
    change (linearGenerators 3 : Mat) * (linearR : Mat) * (linearGenerators 3 : Mat) = _
    rw [linearGenerators_matrix, value_linearR]
    exact Certificate.matrix_trt
  have he' : generators 3 * cubicInverter * generators 3 = cubicInverter := by
    apply Subtype.ext
    change (generators 3).val * cubicInverter.val * (generators 3).val = cubicInverter.val
    simpa only [map_mul, project_linearGenerators, project_linearR] using
      congrArg Matrix.ProjGenLinGroup.mk he
  calc
    cubicInverter * generators 3 * cubicInverter⁻¹ =
      (generators 3)⁻¹ * (generators 3 * cubicInverter * generators 3) *
        cubicInverter⁻¹ := by group
    _ = (generators 3)⁻¹ := by rw [he']; group
end ONan.E9A4.Inverters
