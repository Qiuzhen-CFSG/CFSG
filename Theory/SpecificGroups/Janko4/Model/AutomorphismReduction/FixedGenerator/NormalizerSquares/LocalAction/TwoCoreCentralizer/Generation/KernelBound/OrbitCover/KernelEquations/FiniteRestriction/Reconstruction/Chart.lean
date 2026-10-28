module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineData

/-!
# The single chart defect on the affine direction space

For every matrix in the displayed direction space, the first chart coordinate
of its base image is zero, and its reconstruction error is a scalar multiple
of one fixed nonzero column. The finite identities are checked in the kernel
using packed binary columns, then extended to the span by linearity.

Consequently the affine restriction gives normalization; one additional scalar
vanishing gives reconstruction. Neither premise is assumed to follow from the
exterior stabilizer here. Source matrices and column convention:
KernelEquations/source/README.md and Janko4/Model/Data.lean.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
open Janko4.GeneratorCertificates

private def rowProduct {n : ℕ} (x : ℕ) (rows : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun i : Fin n => if x.testBit i.val then rows.get i else 0))

def directionFirstColumns : Vector ℕ 124 :=
  ⟨#[
    286137742426113,
    1067573245280256,
    0,
    286137742426113,
    286137742426113,
    0,
    286137742426113,
    0,
    286137742426113,
    286137742426113,
    698720428961794,
    0,
    0,
    698720428961794,
    698720428961794,
    0,
    698720428961794,
    0,
    698720428961794,
    698720428961794,
    1000465331359748,
    1067573245280256,
    0,
    1000465331359748,
    1000465331359748,
    0,
    1000465331359748,
    0,
    1000465331359748,
    1000465331359748,
    629051242479624,
    25144069046272,
    1079618900783104,
    39049715617800,
    347365720305672,
    1049581425975296,
    103867521916936,
    37982432649216,
    747092523077640,
    955238555537416,
    255206907162640,
    0,
    0,
    255206907162640,
    255206907162640,
    0,
    255206907162640,
    0,
    255206907162640,
    255206907162640,
    370730899427360,
    1067573245280256,
    0,
    370730899427360,
    370730899427360,
    0,
    370730899427360,
    0,
    370730899427360,
    370730899427360,
    169942528831552,
    25144069046272,
    1079618900783104,
    709263578570816,
    1017584347971648,
    1049581425975296,
    836617643610176,
    37982432649216,
    2111978430528,
    495164582649920,
    919737735614592,
    1086513098211328,
    1079618900783104,
    382504396882048,
    74269187088512,
    1049581425975296,
    323354336784512,
    37982432649216,
    1089733307252864,
    594464411828352,
    239633004179712,
    1067573245280256,
    0,
    239633004179712,
    239633004179712,
    0,
    239633004179712,
    0,
    239633004179712,
    239633004179712,
    426665874264576,
    362642637218304,
    534032283860992,
    119780369318400,
    1092240667348992,
    537655746101248,
    289900136546304,
    874911989924352,
    131654060524032,
    459052765057024,
    413433642296255,
    720460901564830,
    524112084243583,
    523244804977775,
    355268633342624,
    936390742325118,
    662016938628904,
    310870116602276,
    916696417613062,
    101538155235314,
    420378341896229,
    206028873754612,
    387589549740955,
    979452773574008,
    629108452569902,
    251616640103925,
    598458744870006,
    1094300413808988,
    927345826014661,
    507794443325444,
    136257340899546,
    851591049336611,
    605032597911552,
    1067573245280256], rfl⟩

def directionImages : Vector ℕ 124 :=
  ⟨#[
    4386640062819776563682656457422824,
    3140339117071804363174869278202215,
    0,
    4386640062819776563682656457422824,
    4386640062819776563682656457422824,
    0,
    4386640062819776563682656457422824,
    0,
    4386640062819776563682656457422824,
    4386640062819776563682656457422824,
    4272290007034481531043488587988588,
    0,
    0,
    4272290007034481531043488587988588,
    4272290007034481531043488587988588,
    0,
    4272290007034481531043488587988588,
    0,
    4272290007034481531043488587988588,
    4272290007034481531043488587988588,
    850386748495279781903355581050954,
    3140339117071804363174869278202215,
    0,
    850386748495279781903355581050954,
    850386748495279781903355581050954,
    0,
    850386748495279781903355581050954,
    0,
    850386748495279781903355581050954,
    850386748495279781903355581050954,
    1519983227798938834922111978020432,
    2321165111714460623155603122500335,
    2948972452431581975972682120747551,
    925763592103126895367736772671479,
    3206803824073951291516603173157854,
    3058688333184502583134782045281214,
    4292027437663822170231863370031130,
    2348787881697698831259087868331314,
    825476430305125995103327792096026,
    889964495752817625359153097270743,
    4519079663103898473998768708945668,
    0,
    0,
    4519079663103898473998768708945668,
    4519079663103898473998768708945668,
    0,
    4519079663103898473998768708945668,
    0,
    4519079663103898473998768708945668,
    4519079663103898473998768708945668,
    2045910502700286885938374134167749,
    3140339117071804363174869278202215,
    0,
    2045910502700286885938374134167749,
    2045910502700286885938374134167749,
    0,
    2045910502700286885938374134167749,
    0,
    2045910502700286885938374134167749,
    2045910502700286885938374134167749,
    4507150071830902938939706134843820,
    2321165111714460623155603122500335,
    2948972452431581975972682120747551,
    3760811890198865922234957019412491,
    219567268545039364235658766021666,
    3058688333184502583134782045281214,
    1446852779911234970974560937799654,
    2348787881697698831259087868331314,
    3822769933799941422848570882764006,
    3877126542687896138853013297441323,
    122806817540308703344558585699652,
    4718640583816793969308454411840392,
    2948972452431581975972682120747551,
    1974539107927124168327227047146723,
    4277480664766026965973790833670346,
    3058688333184502583134782045281214,
    3232818543419534673671227091608334,
    2348787881697698831259087868331314,
    2034268094774195524159218241413134,
    2091467175364392785266549645059779,
    1751996822732047529656451406365437,
    3140339117071804363174869278202215,
    0,
    1751996822732047529656451406365437,
    1751996822732047529656451406365437,
    0,
    1751996822732047529656451406365437,
    0,
    1751996822732047529656451406365437,
    1751996822732047529656451406365437,
    4580117505501864628170663415009990,
    2426910163422964064323872911838404,
    714118272678581699627203890152887,
    4716780135270119574627368597069998,
    1471796873077595205504226841153321,
    2717583189557042792695336733013642,
    4804719424519092685806663177857368,
    2040066534899981527067414101189104,
    4634513242643704275956101323047831,
    3289596930698296291411844339496017,
    1395481676114634073879422561780166,
    2866146655599132455211601799092067,
    4927881633427662959197293379968880,
    4087168966306654651733278619255620,
    2314948803747659849856546666725602,
    1288689219191266804532451412003150,
    1797642572629545012125150109751943,
    3955347336737019669677574305579937,
    1690915595807961474048472447257701,
    3454942245286197636955086837046836,
    3717073748583952124049964755830961,
    482121569055441131343220664412494,
    4508273708763382487950314549897738,
    2432240332082102548241220065625563,
    623619932569275123003396075182158,
    433363280471771560443651282379303,
    1779644274321360476682886469974966,
    464977607501559085036579378633636,
    4648661218482438235288328428725215,
    547965135425357946402268755306969,
    3739877181744469002490267995036522,
    4123483562492905303940273054772416,
    2994783699482438933728096914306444,
    3140339117071804363174869278202215], rfl⟩

def directionChartCoefficients : Vector ℕ 124 :=
  ⟨#[
    4161344,
    833434,
    0,
    4161344,
    4161344,
    0,
    4161344,
    0,
    4161344,
    4161344,
    1390030,
    0,
    0,
    1390030,
    1390030,
    0,
    1390030,
    0,
    1390030,
    1390030,
    2370190,
    833434,
    0,
    2370190,
    2370190,
    0,
    2370190,
    0,
    2370190,
    2370190,
    2525842,
    1375824,
    3188702,
    3072992,
    3171462,
    1397952,
    858686,
    3449412,
    1316516,
    3580446,
    368640,
    0,
    0,
    368640,
    368640,
    0,
    368640,
    0,
    368640,
    368640,
    1804942,
    833434,
    0,
    1804942,
    1804942,
    0,
    1804942,
    0,
    1804942,
    1804942,
    1149586,
    1375824,
    3188702,
    1696736,
    484486,
    1397952,
    3807806,
    3449412,
    2299556,
    107038,
    1652178,
    1591754,
    3188702,
    1137824,
    1039302,
    1397952,
    3319166,
    3449412,
    2861540,
    597342,
    1272462,
    833434,
    0,
    1272462,
    1272462,
    0,
    1272462,
    0,
    1272462,
    1272462,
    2079034,
    1216642,
    1282648,
    2179536,
    494588,
    814312,
    488214,
    764074,
    4010246,
    1620244,
    1195038,
    3890952,
    998214,
    3346618,
    1590956,
    3953630,
    888936,
    2564192,
    3132318,
    2044986,
    2845812,
    2807306,
    1689264,
    3325594,
    699072,
    2414396,
    2390286,
    761004,
    4169440,
    2910288,
    1201292,
    2764806,
    1727764,
    833434], rfl⟩

def defectColumn : NaturalModule := binaryColumn 327279473999649800678298339

def defectCoordinate : Fin 112 := 0

def baseImage : Matrix (Fin 50) (Fin 50) (ZMod 2) →ₗ[ZMod 2] NaturalModule where
  toFun X := restrictionEmbedding *ᵥ (X *ᵥ Pi.single 0 1)
  map_add' X Y := by simp only [Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c X := by simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, RingHom.id_apply]

def chartMap : NaturalModule →ₗ[ZMod 2] (Fin 22 → ZMod 2) where
  toFun := coordinates
  map_add' u v := by ext i; exact dotProduct_add _ _ _
  map_smul' c v := by ext i; exact dotProduct_smul _ _ _

def synthesisMap : (Fin 22 → ZMod 2) →ₗ[ZMod 2] NaturalModule where
  toFun := synthesize
  map_add' u v := by simp only [synthesize, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [synthesize, Pi.smul_apply, Finset.smul_sum,
    smul_smul, RingHom.id_apply, smul_eq_mul]

/-- Linear failure of reconstruction from the published twenty-two chart columns. -/
def chartDefect : NaturalModule →ₗ[ZMod 2] NaturalModule :=
  LinearMap.id - synthesisMap.comp chartMap

/-- The single scalar error remaining on the candidate affine matrix space. -/
def defectScalar (X : Matrix (Fin 50) (Fin 50) (ZMod 2)) : ZMod 2 :=
  chartDefect (baseImage X) defectCoordinate

theorem chartDefect_apply (v : NaturalModule) :
    chartDefect v = v - synthesize (coordinates v) := rfl

private theorem binaryColumn_rowProduct {n : ℕ} (x : ℕ) (rows : Vector ℕ n) :
    binaryColumn (rowProduct x rows) =
      ∑ i : Fin n, bit x i.val • binaryColumn (rows.get i) := by
  ext j
  change bit (rowProduct x rows) j.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x.testBit i.val <;> simp [bit, h, binaryColumn]

private theorem inclusion_columns : ∀ i : Fin 112, ∀ j : Fin 50,
    restrictionEmbedding i j = binaryColumn (restrictionColumns.get j) i := by
  intro i j
  rfl

private theorem direction_first_columns : ∀ k : Fin 124, ∀ i : Fin 50,
    affineDirection k i 0 = bit (directionFirstColumns.get k) i.val := by decide +kernel

private theorem packed_direction_images : ∀ k : Fin 124,
    rowProduct (directionFirstColumns.get k) restrictionColumns = directionImages.get k := by
  decide +kernel

private theorem baseImage_direction (k : Fin 124) :
    baseImage (affineDirection k) = binaryColumn (directionImages.get k) := by
  rw [← packed_direction_images k, binaryColumn_rowProduct]
  ext i
  change (restrictionEmbedding *ᵥ (affineDirection k *ᵥ Pi.single 0 1)) i = _
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [inclusion_columns, Matrix.col_apply, direction_first_columns]
  exact mul_comm _ _

private theorem direction_chart_coefficients : ∀ k : Fin 124, ∀ i : Fin 22,
    coordinates (binaryColumn (directionImages.get k)) i =
      bit (directionChartCoefficients.get k) i.val := by decide +kernel

private theorem packed_direction_defects : ∀ k : Fin 124,
    directionImages.get k ^^^ rowProduct (directionChartCoefficients.get k) basisColumns =
      if (17552799707978362774193210816690218843 : ℕ).testBit k.val
      then 327279473999649800678298339 else 0 := by decide +kernel

private theorem direction_normalization : ∀ k : Fin 124,
    coordinates (baseImage (affineDirection k)) 0 = 0 := by
  intro k
  rw [baseImage_direction, direction_chart_coefficients]
  revert k
  decide +kernel

private theorem binaryColumn_xor (x y : ℕ) :
    binaryColumn (x ^^^ y) = binaryColumn x + binaryColumn y := by
  ext j
  exact bit_xor x y j.val

private theorem direction_defect (k : Fin 124) :
    chartDefect (baseImage (affineDirection k)) =
      defectScalar (affineDirection k) • defectColumn := by
  have h : chartDefect (baseImage (affineDirection k)) =
      bit 17552799707978362774193210816690218843 k.val • defectColumn := by
    rw [chartDefect_apply, baseImage_direction]
    have hs : synthesize (coordinates (binaryColumn (directionImages.get k))) =
        binaryColumn (rowProduct (directionChartCoefficients.get k) basisColumns) := by
      rw [binaryColumn_rowProduct]
      unfold synthesize
      apply Finset.sum_congr rfl
      intro i _
      rw [direction_chart_coefficients]
      rfl
    rw [hs]
    have hchar : ∀ x y : ZMod 2, x - y = x + y := by decide
    have hsub : ∀ u v : NaturalModule, u - v = u + v := by
      intro u v
      ext i
      exact hchar _ _
    rw [hsub, ← binaryColumn_xor, packed_direction_defects]
    cases hb : (17552799707978362774193210816690218843 : ℕ).testBit k.val
    · simp only [bit, hb, Bool.false_eq_true, ↓reduceIte, zero_smul]
      ext i
      simp [binaryColumn]
    · simp only [bit, hb, ↓reduceIte, one_smul]
      rfl
  have hd : defectColumn defectCoordinate = 1 := by decide +kernel
  have he : defectScalar (affineDirection k) =
      bit 17552799707978362774193210816690218843 k.val := by
    unfold defectScalar
    rw [h, Pi.smul_apply, hd, smul_eq_mul, mul_one]
  rw [he]
  exact h

/-- Every direction has zero normalization coordinate. -/
theorem normalization_of_mem_affineDirections
    {X : Matrix (Fin 50) (Fin 50) (ZMod 2)} (hX : X ∈ affineDirections) :
    coordinates (baseImage X) 0 = 0 := by
  change X ∈ Submodule.span (ZMod 2) (Set.range affineDirection) at hX
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨k, rfl⟩ := hX; exact direction_normalization k
  | zero => change chartMap (baseImage 0) 0 = 0; simp
  | add X Y _ _ hX hY =>
    change chartMap (baseImage (X + Y)) 0 = 0
    simp only [map_add, Pi.add_apply]
    change coordinates (baseImage X) 0 + coordinates (baseImage Y) 0 = 0
    rw [hX, hY, add_zero]
  | smul c X _ hX =>
    change chartMap (baseImage (c • X)) 0 = 0
    simp only [map_smul, Pi.smul_apply]
    change c • coordinates (baseImage X) 0 = 0
    rw [hX, smul_zero]

/-- On the displayed direction space the entire reconstruction error is one
fixed vector multiplied by a scalar. -/
theorem defect_of_mem_affineDirections
    {X : Matrix (Fin 50) (Fin 50) (ZMod 2)} (hX : X ∈ affineDirections) :
    chartDefect (baseImage X) = defectScalar X • defectColumn := by
  change X ∈ Submodule.span (ZMod 2) (Set.range affineDirection) at hX
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨k, rfl⟩ := hX; exact direction_defect k
  | zero => simp [defectScalar]
  | add X Y _ _ hX hY =>
    simpa only [defectScalar, map_add, Pi.add_apply, add_smul] using congrArg₂ (· + ·) hX hY
  | smul c X _ hX =>
    simpa only [defectScalar, map_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
      using congrArg (c • ·) hX

private theorem baseImage_one : baseImage 1 = (baseVector : NaturalModule) := by
  change restrictionEmbedding *ᵥ ((1 : Matrix (Fin 50) (Fin 50) (ZMod 2)) *ᵥ Pi.single 0 1) = _
  rw [Matrix.one_mulVec, restrictionEmbedding_zero]

private theorem chart_base :
    coordinates (baseVector : NaturalModule) = Pi.single 0 1 := by
  have h : (baseVector : NaturalModule) = synthesize (Pi.single 0 1) := by
    simp [synthesize, basisVector_zero]
  rw [h, coordinates_synthesize]

private theorem defect_base : chartDefect (baseVector : NaturalModule) = 0 := by
  rw [chartDefect_apply, chart_base]
  simp [synthesize, basisVector_zero]

private theorem image_difference (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    baseImage (restrictionMatrix g - 1) =
      (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) - (baseVector : NaturalModule) := by
  rw [map_sub, baseImage_one]
  exact congrArg (fun v => v - (baseVector : NaturalModule)) (restrictionImage_matrix g hker)

/-- Normalization follows from the affine restriction alone. -/
theorem matrix_normalization_of_affine (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (haff : AffineRestriction g) :
    coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)) 0 = 1 := by
  have h := normalization_of_mem_affineDirections haff
  rw [image_difference g hker] at h
  change chartMap ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) -
    (baseVector : NaturalModule)) 0 = 0 at h
  rw [map_sub] at h
  change coordinates ((g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)) 0 -
    coordinates (baseVector : NaturalModule) 0 = 0 at h
  rw [chart_base, Pi.single_eq_same] at h
  exact sub_eq_zero.mp h

/-- The reconstruction obligation, after the affine restriction, is exactly
one scalar vanishing. The original exterior hypotheses must still establish
both extra premises before the requested source implication follows. -/
theorem matrix_reconstruction_of_affine_and_scalar (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (haff : AffineRestriction g)
    (hscalar : defectScalar (restrictionMatrix g - 1) = 0) :
    let v := (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule)
    v = synthesize (coordinates v) ∧ coordinates v 0 = 1 := by
  have h := defect_of_mem_affineDirections haff
  rw [hscalar, zero_smul, image_difference g hker, map_sub, defect_base, sub_zero] at h
  rw [chartDefect_apply] at h
  exact ⟨sub_eq_zero.mp h, matrix_normalization_of_affine g hker haff⟩

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
