module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeIndexed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalIndexed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Coverage

/-!
# Candidate filter for the centralizer of the edge reversal

The conjugating word carries a to the fixed reversal. Each of the existing
240 centralizer rows is transported by this word. Rejection points test
normalization of X, and retained rows are indexed in the explicit edge A₅.
The following module checks these candidates against the actual maps.
Source: Aschbacher, *Sporadic Groups*, 47.5 and 47.10; retained ATLAS data.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.EdgeCoverageData
open Theory.GroupTheory GeneratorPair

def moveWord : List (Fin 3) := [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2]
def move : Carrier := evalWord ![a, b, b⁻¹] moveWord

def moveTable : Equiv.Perm (Fin 100) :=
  tablePerm ![66, 50, 27, 88, 63, 84, 67, 76, 97, 96, 8, 39, 6, 25, 58, 19, 93, 37, 12, 17, 26, 61, 57, 55, 91, 98, 81, 65, 2, 1, 42, 28, 20, 72, 87, 52, 35, 79, 62, 78, 77, 68, 74, 49, 43, 53, 9, 45, 92, 36, 70, 41, 47, 85, 23, 29, 38, 69, 73, 80, 24, 51, 95, 0, 13, 15, 71, 56, 21, 48, 7, 4, 5, 30, 64, 86, 89, 46, 60, 31, 22, 82, 32, 33, 83, 44, 18, 16, 10, 54, 94, 34, 99, 11, 59, 75, 3, 40, 14, 90] ![63, 29, 28, 96, 71, 72, 12, 70, 10, 46, 88, 93, 18, 64, 98, 65, 87, 19, 86, 15, 32, 68, 80, 54, 60, 13, 20, 2, 31, 55, 73, 79, 82, 83, 91, 36, 49, 17, 56, 11, 97, 51, 30, 44, 85, 47, 77, 52, 69, 43, 1, 61, 35, 45, 89, 23, 67, 22, 14, 94, 78, 21, 38, 4, 74, 27, 0, 6, 41, 57, 50, 66, 33, 58, 42, 95, 7, 40, 39, 37, 59, 26, 81, 84, 5, 53, 75, 34, 3, 76, 99, 24, 48, 16, 90, 62, 9, 8, 25, 92] (by decide +kernel) (by decide +kernel)

def moveValue : Fin 100 → Fin 100 := EdgeIndexed.unpack 3703128200278496225150390839415050547165231366333297467307136361571392476788653532837339261665830478583412137577022714942874748153005997144756707242856470108151636119118815583251128104056458948573749100449028418
def moveInvValue : Fin 100 → Fin 100 := EdgeIndexed.unpack 3788769261439294997849259134818366162009877845569539362511788739151734447713637086394167749408327257259800168861701927932558873239196205722149494615498956662884776969151102576388668897670539302655236353850543807

def value (i : Fin 240) (p : Fin 100) : Fin 100 :=
  moveValue (SecondOrbitCertificate.conjugatorTableMap i (moveInvValue p))

def xPower (j : Fin 2) (p : Fin 100) : Fin 100 :=
  if j.val = 0 then LocalIndexed.letterValue 0 p
  else LocalIndexed.letterValue 0 (LocalIndexed.letterValue 0 p)

def badPoint (i : Fin 240) (j : Fin 2) : Fin 100 :=
  ⟨(0 >>> (7*(2*i.val+j.val))) % 128 % 100, Nat.mod_lt _ (by decide)⟩

def imageIndex (i : Fin 240) : Fin 60 :=
  ⟨(630421502334814390451497228397829529562626761680270387557706535068469188019568355513792953221878078380544702525458774674444210197361750179548335326759310534607335376513707912837592717770051766460616559542340675298677002561952551625989892249623562124747383272854139131702570980517840828050438370696570270859264 >>> (6*i.val)) % 64 % 60, Nat.mod_lt _ (by decide)⟩

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.EdgeCoverageData
