module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Matrices
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242

/-!
# Native coordinates of the saved 1242 subquotient

The ambient action is the tensor product of the native 44-dimensional module
and its contragredient. Small factor checks and structural tensor rows identify
the saved transposed matrices; the targets are the literal raw ATLAS matrices.
Sources: James (1973), GM02 Proposition 5.1; attribution in source/README.md.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed TensorCoordinates
open SmallModels.FortyFour

def factorLeftAPart0 : List ℕ := 2235532968068 :: 6872021598221 :: 4400198336520 :: 2473903784069 :: 6908688614409 :: 6908697001992 :: 4434860311553 :: 36843175946 :: 4707607904386 :: 4672996245515 :: 36541186760 :: 11709227934404 :: 11819788796036 :: 2510718197772 :: 6597344493709 :: 4553002713088 :: 2235639414789 :: 13651557302405 :: 14605039845508 :: 4398416724489 :: 1099881250826 :: 5635267363331 :: 5809045389963 :: 311486727165 :: 100664205 :: 2510444954124 :: 6597076058758 :: 4432444260395 :: 2510478524423 :: 12075440521985 :: 2235531050636 :: 13615117566602 :: 15934986194978 :: 15575803707395 :: 36849565704 :: 12131476848783 :: 12575969378307 :: 14330198114438 :: 274984419456 :: 2233490018957 :: 6597407490572 :: 8111384838148 :: 1099819384968 :: 7836477833862 :: []

def factorLeftA : List ℕ := factorLeftAPart0

def factorRightAPart0 : List ℕ := 662396682842 :: 9052120679296 :: 12817650907147 :: 6102273517238 :: 8388608 :: 4437573632 :: 8391680 :: 14193890057481 :: 562036736 :: 10449251208192 :: 1073741904 :: 1073741824 :: 555124523008 :: 1073752064 :: 12567892665524 :: 18790481920 :: 1956895139840 :: 11195684039925 :: 2399727365617 :: 13652941048634 :: 15924135442432 :: 12745685033019 :: 14208490109814 :: 16 :: 4294967568 :: 14238015370592 :: 4190040066738 :: 536870960 :: 16612937228736 :: 4294967296 :: 2048 :: 11194610427125 :: 536870912 :: 15569389568 :: 4295002112 :: 753679148529 :: 73551314944 :: 11079407273984 :: 2549914940218 :: 536877056 :: 15633688559616 :: 12762327644219 :: 12247307830134 :: 256087824384 :: []

def factorRightA : List ℕ := factorRightAPart0

private theorem factorLeft_A : matrix 44 44 factorLeftA =
    (KernelAbsolute.Data.matrix 0).transpose := by decide +kernel

private theorem factorRight_A : matrix 44 44 factorRightA =
    KernelAbsolute.Data.matrix 0 := by decide +kernel

/-- Saved ambient transpose, with the inverse in the dual factor retained. -/
theorem native_matrix_A :
    (LinearMap.toMatrix' (action1936 Degree220Pair.generatorA)).transpose =
      matrix 1936 1936 ambientTransposeA := by
  rw [action1936_first, tensorMatrix_transpose, Matrix.transpose_transpose,
    ← factorLeft_A, ← factorRight_A]
  apply tensorMatrix_of_check
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Raw target coordinates; transposing the intertwiner gives the native convention. -/
theorem target_matrix_A : matrix 1242 1242 targetA =
    Degrees12421792.Data1242.first := by
  have h : targetA = Degrees12421792.Data1242.firstRows.toList := by decide +kernel
  rw [h, matrix_array]
  rfl

def factorLeftBPart0 : List ℕ := 5724160 :: 1199104 :: 8120320 :: 1598464 :: 4435075076 :: 16615243791 :: 16058772510 :: 14399605789 :: 12186029083 :: 3328303123 :: 12507185172 :: 4305719296 :: 16264987652 :: 15569765392 :: 14126039060 :: 694116356 :: 9291984900 :: 193946977316 :: 5343373028 :: 1562786254964 :: 4723827594388 :: 189353432096 :: 5561550213680 :: 11557244802324 :: 12741810132 :: 12382346410324 :: 6872386467968 :: 11557746502932 :: 8246438139648 :: 386143220 :: 12611987961184 :: 6921133658260 :: 11814769657136 :: 8380147918624 :: 4983129002 :: 388007065 :: 12348126207 :: 16259311075 :: 6642385873048 :: 12622844522874 :: 8080116530018 :: 6907069333641 :: 2523373250693 :: 8378528660279 :: []

def factorLeftB : List ℕ := factorLeftBPart0

def factorRightBPart0 : List ℕ := 15029428420608 :: 9514588176384 :: 2981183007744 :: 10786239283200 :: 32518907519 :: 4247660850875 :: 15692399336893 :: 12392792276350 :: 8762740421632 :: 16801570914292 :: 8490927873024 :: 4409127862272 :: 3092495757536 :: 7889614892032 :: 6188907957248 :: 12156843392000 :: 17080614669312 :: 5296613645959 :: 16489638053091 :: 10450899607877 :: 15399809761670 :: 14269497028608 :: 13293945612 :: 7971895509837 :: 8002730330121 :: 812936490127 :: 6259928599628 :: 15905344561152 :: 1765575708358 :: 16633835352756 :: 6619564236738 :: 5262321016577 :: 10668698763264 :: 11962268671371 :: 8787522774246 :: 3293287023845 :: 1532235307696 :: 7680800670959 :: 5775759532227 :: 15647109386240 :: 9970459209 :: 15650332209152 :: 11078288010 :: 12615932489728 :: []

def factorRightB : List ℕ := factorRightBPart0

private theorem factorLeft_B : matrix 44 44 factorLeftB =
    (KernelAbsolute.Data.matrix 1).transpose := by decide +kernel

def kernelRowsBPart0 : List ℕ := 15633680958368 :: 10668698764128 :: 13265738388720 :: 3143916061152 :: 9730984011712 :: 10683201486848 :: 1857087602688 :: 7132415262720 :: 10683655651328 :: 9990920470528 :: 186188706250 :: 14568763949511 :: 10518240233473 :: 15334342230620 :: 9836785689183 :: 1979104896692 :: 10661422473813 :: 2206774386695 :: 4707217484865 :: 12929124914684 :: 9906543252799 :: 12831311683140 :: 7696777336757 :: 4408784013312 :: 11475809326144 :: 8846516159392 :: 17366623454048 :: 4278024393968 :: 592424206816 :: 2846687208512 :: 10659233814432 :: 14229425370976 :: 5662916376816 :: 14240162870752 :: 8808984346624 :: 17333422260224 :: 10459319107584 :: 555127275520 :: 8249660669952 :: 8809388965888 :: 10455330848768 :: 17333925969920 :: 12380584017920 :: 555300683776 :: []

def kernelRowsB : List ℕ := kernelRowsBPart0

private theorem kernel_B : matrix 44 44 kernelRowsB = KernelAbsolute.Data.matrix 1 := by
  decide +kernel

private theorem factorRight_B : matrix 44 44 factorRightB =
    KernelAbsolute.Data.matrix 1 ^ 2 := by
  rw [← kernel_B, pow_two]
  symm
  apply matrix_product
  · decide +kernel
  · decide +kernel

/-- Saved ambient transpose, with the inverse in the dual factor retained. -/
theorem native_matrix_B :
    (LinearMap.toMatrix' (action1936 Degree220Pair.generatorB)).transpose =
      matrix 1936 1936 ambientTransposeB := by
  rw [action1936_second, tensorMatrix_transpose, Matrix.transpose_transpose,
    ← factorLeft_B, ← factorRight_B]
  apply tensorMatrix_of_check
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Raw target coordinates; transposing the intertwiner gives the native convention. -/
theorem target_matrix_B : matrix 1242 1242 targetB =
    Degrees12421792.Data1242.second := by
  have h : targetB = Degrees12421792.Data1242.secondRows.toList := by decide +kernel
  rw [h, matrix_array]
  rfl

/-- Density needs only this nonzero entry of the actual quotient map. -/
theorem quotientMap_ne_zero : Matrix.toLin' quotientMap ≠ 0 := by
  intro h
  have hm : quotientMap = 0 := by
    simpa only [LinearMap.toMatrix'_toLin', map_zero] using congrArg LinearMap.toMatrix' h
  have hv : quotientMap 0 232 = 1 := by decide +kernel
  have he := congrArg (fun M : Matrix (Fin 1242) (Fin 1474) (ZMod 2) => M 0 232) hm
  rw [hv, Matrix.zero_apply] at he
  exact one_ne_zero he

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
