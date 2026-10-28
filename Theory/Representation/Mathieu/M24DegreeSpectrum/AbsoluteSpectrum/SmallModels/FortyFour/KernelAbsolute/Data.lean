module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic

/-!
# Binary matrix witnesses for the native Golay exterior kernel

The columns below are the saved native coordinate witnesses, with bit i of
column j representing entry (i,j). They are definitions, not assertions about
the native action. The comparison must be proved using the actual contraction
kernel. The independent density certificate uses these precise matrices.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1, manuscript p.17.
Witness provenance and regeneration are described in `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Data

abbrev Space := Fin 44 → ZMod 2
abbrev Mat := Matrix (Fin 44) (Fin 44) (ZMod 2)

def bit (x i : ℕ) : ZMod 2 := if x.testBit i then 1 else 0

def aColumns : List ℕ := [2235532968068, 6872021598221, 4400198336520, 2473903784069, 6908688614409, 6908697001992, 4434860311553, 36843175946, 4707607904386, 4672996245515, 36541186760, 11709227934404, 11819788796036, 2510718197772, 6597344493709, 4553002713088, 2235639414789, 13651557302405, 14605039845508, 4398416724489, 1099881250826, 5635267363331, 5809045389963, 311486727165, 100664205, 2510444954124, 6597076058758, 4432444260395, 2510478524423, 12075440521985, 2235531050636, 13615117566602, 15934986194978, 15575803707395, 36849565704, 12131476848783, 12575969378307, 14330198114438, 274984419456, 2233490018957, 6597407490572, 8111384838148, 1099819384968, 7836477833862]

def bColumns : List ℕ := [5724160, 1199104, 8120320, 1598464, 4435075076, 16615243791, 16058772510, 14399605789, 12186029083, 3328303123, 12507185172, 4305719296, 16264987652, 15569765392, 14126039060, 694116356, 9291984900, 193946977316, 5343373028, 1562786254964, 4723827594388, 189353432096, 5561550213680, 11557244802324, 12741810132, 12382346410324, 6872386467968, 11557746502932, 8246438139648, 386143220, 12611987961184, 6921133658260, 11814769657136, 8380147918624, 4983129002, 388007065, 12348126207, 16259311075, 6642385873048, 12622844522874, 8080116530018, 6907069333641, 2523373250693, 8378528660279]

def columns (j : Fin 2) : List ℕ := ![aColumns, bColumns] j

/-- The literal candidate matrices, acting on column vectors. -/
def matrix (j : Fin 2) : Mat :=
  fun x y => bit ((columns j)[y.val]?.getD 0) x.val

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Data
