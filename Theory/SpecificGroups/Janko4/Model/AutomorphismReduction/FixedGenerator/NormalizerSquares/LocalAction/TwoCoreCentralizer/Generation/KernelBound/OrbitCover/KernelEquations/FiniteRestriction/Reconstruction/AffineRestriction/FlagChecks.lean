module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch000
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch008
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch016
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch024
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch032
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch040
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch048
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch056
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch064
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch072
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch080
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch088
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch096
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch104
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch112
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks.Batch120

/-!
# The certified flag

All 124 affine directions become strictly upper triangular.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
open LinearMembership GeneratorCertificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flagInverse_mul_flag : flagInverse * flagMatrix = 1 := by
  rw [flagInverse, flagMatrix, ← rectDecode_one 50]
  apply rectProduct_eq
  simp only [get_ofFn]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flag_mul_flagInverse : flagMatrix * flagInverse = 1 := by
  rw [flagInverse, flagMatrix, ← rectDecode_one 50]
  apply rectProduct_eq
  simp only [get_ofFn]
  decide +kernel

theorem flagConjugation_one : flagConjugation 1 = 1 := by
  change flagInverse * 1 * flagMatrix = 1
  rw [Matrix.mul_one, flagInverse_mul_flag]

theorem affineDirection_strict (k : Fin 124) :
    ∀ i j : Fin 50, j ≤ i → flagConjugation (affineDirection k) i j = 0 := by
  fin_cases k
  · exact direction_strict_0 0
  · exact direction_strict_0 1
  · exact direction_strict_0 2
  · exact direction_strict_0 3
  · exact direction_strict_0 4
  · exact direction_strict_0 5
  · exact direction_strict_0 6
  · exact direction_strict_0 7
  · exact direction_strict_8 0
  · exact direction_strict_8 1
  · exact direction_strict_8 2
  · exact direction_strict_8 3
  · exact direction_strict_8 4
  · exact direction_strict_8 5
  · exact direction_strict_8 6
  · exact direction_strict_8 7
  · exact direction_strict_16 0
  · exact direction_strict_16 1
  · exact direction_strict_16 2
  · exact direction_strict_16 3
  · exact direction_strict_16 4
  · exact direction_strict_16 5
  · exact direction_strict_16 6
  · exact direction_strict_16 7
  · exact direction_strict_24 0
  · exact direction_strict_24 1
  · exact direction_strict_24 2
  · exact direction_strict_24 3
  · exact direction_strict_24 4
  · exact direction_strict_24 5
  · exact direction_strict_24 6
  · exact direction_strict_24 7
  · exact direction_strict_32 0
  · exact direction_strict_32 1
  · exact direction_strict_32 2
  · exact direction_strict_32 3
  · exact direction_strict_32 4
  · exact direction_strict_32 5
  · exact direction_strict_32 6
  · exact direction_strict_32 7
  · exact direction_strict_40 0
  · exact direction_strict_40 1
  · exact direction_strict_40 2
  · exact direction_strict_40 3
  · exact direction_strict_40 4
  · exact direction_strict_40 5
  · exact direction_strict_40 6
  · exact direction_strict_40 7
  · exact direction_strict_48 0
  · exact direction_strict_48 1
  · exact direction_strict_48 2
  · exact direction_strict_48 3
  · exact direction_strict_48 4
  · exact direction_strict_48 5
  · exact direction_strict_48 6
  · exact direction_strict_48 7
  · exact direction_strict_56 0
  · exact direction_strict_56 1
  · exact direction_strict_56 2
  · exact direction_strict_56 3
  · exact direction_strict_56 4
  · exact direction_strict_56 5
  · exact direction_strict_56 6
  · exact direction_strict_56 7
  · exact direction_strict_64 0
  · exact direction_strict_64 1
  · exact direction_strict_64 2
  · exact direction_strict_64 3
  · exact direction_strict_64 4
  · exact direction_strict_64 5
  · exact direction_strict_64 6
  · exact direction_strict_64 7
  · exact direction_strict_72 0
  · exact direction_strict_72 1
  · exact direction_strict_72 2
  · exact direction_strict_72 3
  · exact direction_strict_72 4
  · exact direction_strict_72 5
  · exact direction_strict_72 6
  · exact direction_strict_72 7
  · exact direction_strict_80 0
  · exact direction_strict_80 1
  · exact direction_strict_80 2
  · exact direction_strict_80 3
  · exact direction_strict_80 4
  · exact direction_strict_80 5
  · exact direction_strict_80 6
  · exact direction_strict_80 7
  · exact direction_strict_88 0
  · exact direction_strict_88 1
  · exact direction_strict_88 2
  · exact direction_strict_88 3
  · exact direction_strict_88 4
  · exact direction_strict_88 5
  · exact direction_strict_88 6
  · exact direction_strict_88 7
  · exact direction_strict_96 0
  · exact direction_strict_96 1
  · exact direction_strict_96 2
  · exact direction_strict_96 3
  · exact direction_strict_96 4
  · exact direction_strict_96 5
  · exact direction_strict_96 6
  · exact direction_strict_96 7
  · exact direction_strict_104 0
  · exact direction_strict_104 1
  · exact direction_strict_104 2
  · exact direction_strict_104 3
  · exact direction_strict_104 4
  · exact direction_strict_104 5
  · exact direction_strict_104 6
  · exact direction_strict_104 7
  · exact direction_strict_112 0
  · exact direction_strict_112 1
  · exact direction_strict_112 2
  · exact direction_strict_112 3
  · exact direction_strict_112 4
  · exact direction_strict_112 5
  · exact direction_strict_112 6
  · exact direction_strict_112 7
  · exact direction_strict_120 0
  · exact direction_strict_120 1
  · exact direction_strict_120 2
  · exact direction_strict_120 3

def scalarLeftRows : Vector (Vector ℕ 50) 2 :=
  ⟨#[⟨#[872026229288132, 1028607789761431, 514883624454663, 773884658833360, 274735539148747, 895811457535315, 752167982875995, 78234180378547, 410439685391920, 550762564287936, 872744239938745, 1028373265025641, 550667125551719, 773292001963393, 274409255909178, 860819876562083, 752898624242595, 78211295385001, 375014260491129, 464610393264440, 550762537313828, 636048579726467, 767958798437939, 561693858699036, 1102134104947387, 1099572347658260, 642614032624120, 99199641623691, 863789882234670, 363223155360951, 538705642680070, 262952566815402, 355860717407977, 87148846344829, 292332382865190, 90553599091551, 637608117582089, 464757379237243, 1121225442761333, 307875540707304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩, ⟨#[800702144940402, 216064019446868, 606055972005614, 624399861091426, 1025977803958852, 347817737224177, 810988257582740, 1095015984771291, 664689610120888, 483287215677024, 801490011633705, 216333898006042, 571463939851137, 588378008803017, 990670996800661, 313220686128563, 776101881816946, 1095076006405158, 664424641244036, 1013289475357229, 483295936148982, 537123938191055, 1101068098261469, 214756311770885, 917192983795128, 513233326472944, 55747264729067, 51835439564489, 958147854508617, 499474338425295, 182162602764070, 482902260606389, 300035342391356, 1077315585402273, 980787791016895, 834399577464616, 670579395442661, 383127646669095, 168026523220551, 951489237236381, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩], rfl⟩

def scalarConjugateRows : Vector (Vector ℕ 50) 2 :=
  ⟨#[⟨#[779412484256769, 447617501231106, 7728875536388, 510228859274248, 505089186055184, 373374595874848, 382052542963776, 478510714480768, 52783941494016, 1055593145012736, 766359604559872, 115448720916480, 676199651082240, 986261930115072, 908196604542976, 179220395327488, 460695372038144, 467292441804800, 414515883671552, 343047627866112, 602532372021248, 144036023238656, 56075093016576, 312261302288384, 768558627815424, 584940185976832, 1117103813820416, 152832116260864, 332052511588352, 201210627883008, 851021999898624, 749866930143232, 256186209271808, 700388906893312, 323256418566144, 948878534770688, 854320534781952, 416714906927104, 128642860449792, 1099511627776000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩, ⟨#[407120264914944, 656305631604736, 825042809498624, 107852960795648, 637757004907520, 1110491164936192, 162864839432192, 803856184374272, 203248620335104, 105695449864192, 608029930161152, 591537255745536, 423311976697856, 221001837191168, 163827232555008, 1041237511536640, 969769255763968, 604731395407872, 989560465260544, 612427977195520, 1114904791613440, 227598909046784, 524467050643456, 849922496659456, 483785132998656, 826832777641984, 539860276346880, 221001971400704, 643214570684416, 1072024373952512, 886207445729280, 1043438682243072, 65974992633856, 1021454892138496, 1054448830906368, 325489801560064, 1096281812369408, 324493369147392, 641290156900352, 736123034796032, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩], rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scalarDirection_conjugation (k : Fin 2) :
    flagConjugation (scalarDirection k) = rectDecode 50 (scalarConjugateRows.get k) := by
  apply conjugation_eq_of_products (scalarDirection k)
    (matrixSlices (scalarDirectionRows.get k)) (scalarLeftRows.get k)
    (scalarConjugateRows.get k)
  · exact scalarDirection_eq_slices k
  · have h : ∀ (k : Fin 2) (i : Fin 50),
        rowScan (flagInverseRows.get i)
          (matrixSlices (scalarDirectionRows.get k)).toList =
          (scalarLeftRows.get k).get i := by
      simp only [matrixSlices, Vector.toList_ofFn]
      decide +kernel
    exact h k
  · have h : ∀ (k : Fin 2) (i : Fin 50),
        rowScan ((scalarLeftRows.get k).get i) flagRows.toList =
          (scalarConjugateRows.get k).get i := by decide +kernel
    exact h k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scalarDirection_upper (k : Fin 2) :
    (flagConjugation (scalarDirection k)).IsUpperTriangular := by
  rw [scalarDirection_conjugation]
  intro i j hij
  have h : ∀ (k : Fin 2) (i : Fin 50),
      (scalarConjugateRows.get k).get i % 2 ^ i.val = 0 := by decide +kernel
  have heq := congrArg (fun x : ℕ => x.testBit j.val) (h k i)
  have hlt : j.val < i.val := hij
  simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and,
    Nat.zero_testBit] at heq
  simp only [rectDecode, bit, heq, Bool.false_eq_true, ↓reduceIte]

theorem scalarDirection_diagonal (k : Fin 2) (i : Fin 50) :
    flagConjugation (scalarDirection k) i i =
      if k = 0 then (if i.val < 10 then 1 else 0)
      else (if 10 ≤ i.val ∧ i.val < 40 then 1 else 0) := by
  rw [scalarDirection_conjugation]
  have h : ∀ (k : Fin 2) (i : Fin 50),
      rectDecode 50 (scalarConjugateRows.get k) i i =
        if k = 0 then (if i.val < 10 then 1 else 0)
        else (if 10 ≤ i.val ∧ i.val < 40 then 1 else 0) := by decide +kernel
  exact h k i

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
