module

public import Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators
import all Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
import all Theory.SpecificGroups.MathieuAmalgamCompletion.Relators

/-!
# Finite canonical equations for the six exterior-cubic defects

The split affine calculation is reduced to the sixteen translations above the
canonical marked pair.  This file only records the finite certificate; the
transport to an arbitrary marked pair is in the parent file.
-/

public noncomputable section
open Equiv Subgroup Subgroup.CosetWordCertificate
open Matrix.PSL3Four.MathieuAmalgamMarking
namespace Theory.SpecificGroups.SymmetricSix.HexadSixDefects
open HexadCubicWord HexadAffineNineteen
open Theory.SpecificGroups.MathieuAmalgamCompletion
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

private abbrev oneRaw : Raw := (0,1)
private def canonical (w : Fin 16) : Fin 4 → Raw :=
  ![(0,a0),(w,b0),(0,1),(lin 3 11 10 13 w,c2)]
private def defect (w : Fin 16) (i : Fin 27) : Raw :=
  ev (canonical w) (relator i)
private def conj (x y : Raw) : Raw := mul (mul x y) (inv x)
private def ab (w : Fin 16) : Raw := mul (canonical w 0) (canonical w 1)
private def baInv (w : Fin 16) : Raw := mul (canonical w 1) (inv (canonical w 0))
private def nanInv (w : Fin 16) : Raw :=
  mul (mul (canonical w 3) (canonical w 0)) (inv (canonical w 3))
private def abab (w : Fin 16) : Raw :=
  mul (mul (mul (canonical w 0) (canonical w 1)) (canonical w 0)) (canonical w 1)
private def abnInvA (w : Fin 16) : Raw :=
  mul (mul (mul (canonical w 0) (canonical w 1)) (inv (canonical w 3))) (canonical w 0)
private def nInvAb (w : Fin 16) : Raw :=
  mul (mul (inv (canonical w 3)) (canonical w 0)) (canonical w 1)

/-- Exact finite identities among all six actual lifted words.

The right-hand sides are products of literal conjugates of word 17. -/
private theorem equations (w : Fin 16) :
    defect w 18 = mul (conj (ab w) (defect w 17)) (conj (baInv w) (defect w 17)) ∧
    defect w 20 = mul (conj (canonical w 0) (defect w 17)) (conj (nanInv w) (defect w 17)) ∧
    defect w 21 = mul (defect w 17) (conj (abab w) (defect w 17)) ∧
    defect w 22 = mul (defect w 17) (conj (abnInvA w) (defect w 17)) ∧
    defect w 24 = mul (conj (inv (canonical w 0)) (defect w 17))
      (conj (nInvAb w) (defect w 17)) := by
  decide +kernel +revert


/-- The two quotient checks in the canonical model select `c2`. -/
private theorem selected_c2 (n : S6)
    (hn3 : n^3=1)
    (hcomm : n * eval ![a0,b0] torusWord = eval ![a0,b0] torusWord * n)
    (hquot19 : (b0*n*a0⁻¹)^4=1)
    (hquot17 : eval ![a0,b0,1,n] (relator 17)=1) : n=c2 := by
  rcases candidates n hn3 hcomm hquot19 with h1|h2|h3
  · rw [h1] at hquot17
    exfalso
    revert hquot17
    decide +kernel
  · exact h2
  · rw [h3] at hquot17
    exfalso
    revert hquot17
    decide +kernel

end Theory.SpecificGroups.SymmetricSix.HexadSixDefects
