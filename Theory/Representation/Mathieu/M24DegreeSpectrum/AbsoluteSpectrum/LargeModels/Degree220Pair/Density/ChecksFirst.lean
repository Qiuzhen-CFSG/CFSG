module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Witnesses
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Recurrences

/-!
# Kernel checks for the first degree-220 pair

A full dense product was benchmarked at 2.72 GB peak RSS. Sequential
elaboration bounds temporary reduction memory across these certificates.
There are no raised resource limits or external decision procedures.
Source and reproduction: Density/source/README.md.
-/

set_option Elab.async false
public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.ChecksFirst
open Packed Witnesses.First

theorem a_rows : checkRows 220 a firstRowsA = true := by decide +kernel

theorem b_rows : checkRows 220 b firstRowsB = true := by decide +kernel

theorem bs_eq : bs = b := by decide +kernel

theorem ab_mul : checkMul 220 a bs ab = true := by decide +kernel

theorem ab2_mul : checkMul 220 ab ab ab2 = true := by decide +kernel

theorem ab3_mul : checkMul 220 ab2 ab ab3 = true := by decide +kernel

theorem word_mul : checkMul 220 ab3 a word = true := by decide +kernel

theorem sum_add : checkAdd 220 a bs sumAB = true := by decide +kernel

theorem c_add : checkAdd 220 sumAB word c = true := by decide +kernel

theorem a_transpose : checkTranspose 220 aT a = true := by decide +kernel

theorem b_transpose : checkTranspose 220 bT b = true := by decide +kernel

theorem c_transpose : checkTranspose 220 cT c = true := by decide +kernel

theorem l_transpose : checkTranspose 220 l p = true := by decide +kernel

theorem e_outer : checkOuter 220 e v lam = true := by decide +kernel

theorem x_cyclic : checkCyclic 220 c x seed = true := by decide +kernel

theorem x_inverse : checkInverse 220 xi x = true := by decide +kernel

theorem p_inverse : checkInverse 220 p pi = true := by decide +kernel

theorem q_inverse : checkInverse 220 qi q = true := by decide +kernel

theorem v_kernel : row 220 v cT 220 = 0 := by decide +kernel

theorem lam_kernel : row 220 lam c 220 = 0 := by decide +kernel

theorem left_orbit : checkOrbit 220 a b l lam parentsL lettersL = true := by decide +kernel

theorem right_orbit : checkOrbit 220 aT bT q v parentsR lettersR = true := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.ChecksFirst
