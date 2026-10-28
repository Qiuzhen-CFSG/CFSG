module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.Construction
public import Theory.Representation.RepEquiv
public import Mathlib.Tactic.LinearCombination
/-!
# Reconstruction of every octonion derivation

The Leibniz equations on standard basis products determine every matrix entry
from the fourteen read by `params`. Each displayed relation is obtained from
one basis product, and each reconstruction equation combines at most five such
relations. We assemble the eight rows by linear-map extensionality, obtaining
both inverses, dimension fourteen, and transport of the actual adjoint action.

Source: GLS3, Examples 1.14.9(c) and 2.8.10(g), using the literal ATLAS
split-octonion table. The basis equations retain that multiplication throughout.
-/

-- Serial elaboration avoids the measured declaration-parallelism overhead.
set_option Elab.async false
@[expose] public section
namespace Atlas.G2.Restricted.Adjoint.Coordinates
open Atlas.SplitOctonion
variable {F : Type*} [Field F] [CharP F 2]
private theorem leibniz_0_7_at_3 (D : Adjoint.Space F) :
    entry D.val 3 3 = entry D.val 0 0 + entry D.val 7 7 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 3
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_3_at_1 (D : Adjoint.Space F) :
    entry D.val 1 1 = entry D.val 1 1 + entry D.val 3 3 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 3) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 3)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_2 (D : Adjoint.Space F) :
    entry D.val 2 3 = entry D.val 6 7 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_3_at_0 (D : Adjoint.Space F) :
    entry D.val 0 1 = entry D.val 2 3 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 3) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 3)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_1 (D : Adjoint.Space F) :
    entry D.val 1 3 = entry D.val 5 7 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_2_3_at_0 (D : Adjoint.Space F) :
    entry D.val 0 2 = entry D.val 1 3 := by
  have hp : mul (basisVector (F := F) 2) (basisVector (F := F) 3) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 2) (basisVector (F := F) 3)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_0 (D : Adjoint.Space F) :
    entry D.val 0 3 = entry D.val 4 7 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_3_4_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 0 3 + entry D.val 0 4 := by
  have hp : mul (basisVector (F := F) 3) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 3) (basisVector (F := F) 4)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_7_at_0 (D : Adjoint.Space F) :
    entry D.val 0 5 = entry D.val 2 7 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 7) = (basisVector (F := F) 5) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 7)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_2_7_at_0 (D : Adjoint.Space F) :
    entry D.val 0 6 = entry D.val 1 7 := by
  have hp : mul (basisVector (F := F) 2) (basisVector (F := F) 7) = (basisVector (F := F) 6) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 2) (basisVector (F := F) 7)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_3_7_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 0 7 := by
  have hp : mul (basisVector (F := F) 3) (basisVector (F := F) 7) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 3) (basisVector (F := F) 7)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_6_at_3 (D : Adjoint.Space F) :
    entry D.val 3 2 = entry D.val 7 6 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 6) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 6)) 3
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_2_at_1 (D : Adjoint.Space F) :
    entry D.val 1 0 = entry D.val 3 2 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 2) = (basisVector (F := F) 0) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 2)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_6_at_2 (D : Adjoint.Space F) :
    entry D.val 2 2 = entry D.val 0 0 + entry D.val 6 6 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 6) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 6)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_2_at_0 (D : Adjoint.Space F) :
    entry D.val 0 0 = entry D.val 1 1 + entry D.val 2 2 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 2) = (basisVector (F := F) 0) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 2)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_6_at_1 (D : Adjoint.Space F) :
    entry D.val 1 2 = entry D.val 5 6 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 6) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 6)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_2_4_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 0 2 + entry D.val 1 4 := by
  have hp : mul (basisVector (F := F) 2) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 2) (basisVector (F := F) 4)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_2_5_at_0 (D : Adjoint.Space F) :
    entry D.val 0 4 = entry D.val 1 5 := by
  have hp : mul (basisVector (F := F) 2) (basisVector (F := F) 5) = (basisVector (F := F) 4) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 2) (basisVector (F := F) 5)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_2_6_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 1 6 := by
  have hp : mul (basisVector (F := F) 2) (basisVector (F := F) 6) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 2) (basisVector (F := F) 6)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_5_at_3 (D : Adjoint.Space F) :
    entry D.val 3 1 = entry D.val 7 5 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 5) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 5)) 3
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_0_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 2 0 + entry D.val 3 1 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 0) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 0)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_5_at_2 (D : Adjoint.Space F) :
    entry D.val 2 1 = entry D.val 6 5 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 5) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 5)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_4_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 0 1 + entry D.val 2 4 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 4)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_5_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 2 5 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 5) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 5)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_6_at_0 (D : Adjoint.Space F) :
    entry D.val 0 4 = entry D.val 2 6 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 6) = (basisVector (F := F) 4) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 6)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_0_at_1 (D : Adjoint.Space F) :
    0 = entry D.val 3 0 + entry D.val 5 1 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 0) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 0)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_4_at_5 (D : Adjoint.Space F) :
    0 = entry D.val 7 4 + entry D.val 5 1 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 4)) 5
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_4_at_1 (D : Adjoint.Space F) :
    0 = entry D.val 3 4 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 4)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_5_at_1 (D : Adjoint.Space F) :
    0 = entry D.val 0 1 + entry D.val 3 5 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 5) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 5)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_6_at_1 (D : Adjoint.Space F) :
    entry D.val 1 4 = entry D.val 3 6 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 6) = (basisVector (F := F) 4) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 6)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_7_at_1 (D : Adjoint.Space F) :
    entry D.val 1 5 = entry D.val 3 7 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 7) = (basisVector (F := F) 5) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 7)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_0_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 4 0 + entry D.val 3 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 0) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 0)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_1_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 4 1 + entry D.val 2 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 1) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 1)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_2_at_0 (D : Adjoint.Space F) :
    0 = entry D.val 4 2 + entry D.val 1 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 2) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 2)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_4 (D : Adjoint.Space F) :
    entry D.val 4 3 = 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 4
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_4_at_0 (D : Adjoint.Space F) :
    entry D.val 0 0 = entry D.val 0 0 + entry D.val 4 4 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 4) = (basisVector (F := F) 0) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 4)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_5_at_0 (D : Adjoint.Space F) :
    entry D.val 0 1 = entry D.val 4 5 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 5) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 5)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_6_at_0 (D : Adjoint.Space F) :
    entry D.val 0 2 = entry D.val 4 6 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 6) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 6)) 0
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_6_at_7 (D : Adjoint.Space F) :
    entry D.val 7 2 = entry D.val 5 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 6) = (basisVector (F := F) 2) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 6)) 7
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_2_at_1 (D : Adjoint.Space F) :
    0 = entry D.val 5 2 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 2) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 2)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_5 (D : Adjoint.Space F) :
    entry D.val 5 3 = entry D.val 1 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 5
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_4_at_1 (D : Adjoint.Space F) :
    entry D.val 1 0 = entry D.val 5 4 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 4) = (basisVector (F := F) 0) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 4)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_5_at_1 (D : Adjoint.Space F) :
    entry D.val 1 1 = entry D.val 0 0 + entry D.val 5 5 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 5) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 5)) 1
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_5_at_7 (D : Adjoint.Space F) :
    entry D.val 7 1 = entry D.val 6 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 5) = (basisVector (F := F) 1) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 5)) 7
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_0_at_2 (D : Adjoint.Space F) :
    0 = entry D.val 6 1 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 0) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 0)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_2_at_2 (D : Adjoint.Space F) :
    0 = entry D.val 6 2 + entry D.val 4 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 2) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 2)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_3_at_2 (D : Adjoint.Space F) :
    0 = entry D.val 6 3 + entry D.val 2 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 3) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 3)) 2
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_1_4_at_4 (D : Adjoint.Space F) :
    0 = entry D.val 6 4 + entry D.val 4 1 := by
  have hp : mul (basisVector (F := F) 1) (basisVector (F := F) 4) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 1) (basisVector (F := F) 4)) 4
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_0_at_4 (D : Adjoint.Space F) :
    0 = entry D.val 7 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 0) = (0 : Carrier F) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 0)) 4
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem leibniz_0_7_at_7 (D : Adjoint.Space F) :
    entry D.val 7 3 = entry D.val 4 0 := by
  have hp : mul (basisVector (F := F) 0) (basisVector (F := F) 7) = (basisVector (F := F) 3) := by
    ext k; fin_cases k <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h := congrFun (Adjoint.leibniz F D (basisVector (F := F) 0) (basisVector (F := F) 7)) 7
  rw [hp] at h
  simpa [entry, mul, basisVector, CharTwo.neg_eq, add_comm] using h

private theorem entry_0_0 (D : Adjoint.Space F) :
    entry D.val 0 0 = entry D.val 7 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_3 D) + (leibniz_1_3_at_1 D)

private theorem entry_0_1 (D : Adjoint.Space F) :
    entry D.val 0 1 = entry D.val 6 7 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_2 D) + (leibniz_1_3_at_0 D)

private theorem entry_0_2 (D : Adjoint.Space F) :
    entry D.val 0 2 = entry D.val 5 7 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_1 D) + (leibniz_2_3_at_0 D)

private theorem entry_0_3 (D : Adjoint.Space F) :
    entry D.val 0 3 = entry D.val 4 7 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_0 D)

private theorem entry_0_4 (D : Adjoint.Space F) :
    entry D.val 0 4 = entry D.val 4 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_0 D) + (leibniz_3_4_at_0 D)

private theorem entry_0_5 (D : Adjoint.Space F) :
    entry D.val 0 5 = entry D.val 2 7 := by
  linear_combination (norm := ring_nf) (leibniz_1_7_at_0 D)

private theorem entry_0_6 (D : Adjoint.Space F) :
    entry D.val 0 6 = entry D.val 1 7 := by
  linear_combination (norm := ring_nf) (leibniz_2_7_at_0 D)

private theorem entry_0_7 (D : Adjoint.Space F) :
    entry D.val 0 7 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_3_7_at_0 D)

private theorem entry_1_0 (D : Adjoint.Space F) :
    entry D.val 1 0 = entry D.val 7 6 := by
  linear_combination (norm := ring_nf) (leibniz_0_6_at_3 D) + (leibniz_1_2_at_1 D)

private theorem entry_1_1 (D : Adjoint.Space F) :
    entry D.val 1 1 = entry D.val 6 6 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_6_at_2 D) + (leibniz_1_2_at_0 D)

private theorem entry_1_2 (D : Adjoint.Space F) :
    entry D.val 1 2 = entry D.val 5 6 := by
  linear_combination (norm := ring_nf) (leibniz_0_6_at_1 D)

private theorem entry_1_3 (D : Adjoint.Space F) :
    entry D.val 1 3 = entry D.val 5 7 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_1 D)

private theorem entry_1_4 (D : Adjoint.Space F) :
    entry D.val 1 4 = entry D.val 5 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_1 D) + (leibniz_2_3_at_0 D) + (leibniz_2_4_at_0 D)

private theorem entry_1_5 (D : Adjoint.Space F) :
    entry D.val 1 5 = entry D.val 4 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_0 D) + (leibniz_2_5_at_0 D) + (leibniz_3_4_at_0 D)

private theorem entry_1_6 (D : Adjoint.Space F) :
    entry D.val 1 6 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_2_6_at_0 D)

private theorem entry_2_0 (D : Adjoint.Space F) :
    entry D.val 2 0 = entry D.val 7 5 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_5_at_3 D) + (leibniz_1_0_at_0 D)

private theorem entry_2_1 (D : Adjoint.Space F) :
    entry D.val 2 1 = entry D.val 6 5 := by
  linear_combination (norm := ring_nf) (leibniz_0_5_at_2 D)

private theorem entry_2_2 (D : Adjoint.Space F) :
    entry D.val 2 2 = entry D.val 6 6 + entry D.val 7 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_6_at_2 D) + (leibniz_0_7_at_3 D) + (leibniz_1_3_at_1 D)

private theorem entry_2_3 (D : Adjoint.Space F) :
    entry D.val 2 3 = entry D.val 6 7 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_2 D)

private theorem entry_2_4 (D : Adjoint.Space F) :
    entry D.val 2 4 = entry D.val 6 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_2 D) + (leibniz_1_3_at_0 D) + (leibniz_1_4_at_0 D)

private theorem entry_2_5 (D : Adjoint.Space F) :
    entry D.val 2 5 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_5_at_0 D)

private theorem entry_2_6 (D : Adjoint.Space F) :
    entry D.val 2 6 = entry D.val 4 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_0 D) + (leibniz_1_6_at_0 D) + (leibniz_3_4_at_0 D)

private theorem entry_3_0 (D : Adjoint.Space F) :
    entry D.val 3 0 = entry D.val 7 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_0_at_1 D) + (leibniz_1_4_at_5 D)

private theorem entry_3_1 (D : Adjoint.Space F) :
    entry D.val 3 1 = entry D.val 7 5 := by
  linear_combination (norm := ring_nf) (leibniz_0_5_at_3 D)

private theorem entry_3_2 (D : Adjoint.Space F) :
    entry D.val 3 2 = entry D.val 7 6 := by
  linear_combination (norm := ring_nf) (leibniz_0_6_at_3 D)

private theorem entry_3_3 (D : Adjoint.Space F) :
    entry D.val 3 3 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_3_at_1 D)

private theorem entry_3_4 (D : Adjoint.Space F) :
    entry D.val 3 4 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_4_at_1 D)

private theorem entry_3_5 (D : Adjoint.Space F) :
    entry D.val 3 5 = entry D.val 6 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_2 D) + (leibniz_1_3_at_0 D) + (leibniz_1_5_at_1 D)

private theorem entry_3_6 (D : Adjoint.Space F) :
    entry D.val 3 6 = entry D.val 5 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_1 D) + (leibniz_1_6_at_1 D) + (leibniz_2_3_at_0 D) + (leibniz_2_4_at_0 D)

private theorem entry_3_7 (D : Adjoint.Space F) :
    entry D.val 3 7 = entry D.val 4 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_7_at_0 D) + (leibniz_1_7_at_1 D) + (leibniz_2_5_at_0 D) + (leibniz_3_4_at_0 D)

private theorem entry_4_0 (D : Adjoint.Space F) :
    entry D.val 4 0 = entry D.val 7 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_0_at_0 D) + (leibniz_1_0_at_1 D) + (leibniz_1_4_at_5 D)

private theorem entry_4_1 (D : Adjoint.Space F) :
    entry D.val 4 1 = entry D.val 7 5 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_1_at_0 D) + (leibniz_0_5_at_3 D) + (leibniz_1_0_at_0 D)

private theorem entry_4_2 (D : Adjoint.Space F) :
    entry D.val 4 2 = entry D.val 7 6 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_2_at_0 D) + (leibniz_0_6_at_3 D) + (leibniz_1_2_at_1 D)

private theorem entry_4_3 (D : Adjoint.Space F) :
    entry D.val 4 3 = 0 := by
  linear_combination (norm := ring_nf) (leibniz_0_7_at_4 D)

private theorem entry_4_4 (D : Adjoint.Space F) :
    entry D.val 4 4 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_4_at_0 D)

private theorem entry_4_5 (D : Adjoint.Space F) :
    entry D.val 4 5 = entry D.val 6 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_5_at_0 D) + (leibniz_0_7_at_2 D) + (leibniz_1_3_at_0 D)

private theorem entry_4_6 (D : Adjoint.Space F) :
    entry D.val 4 6 = entry D.val 5 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_6_at_0 D) + (leibniz_0_7_at_1 D) + (leibniz_2_3_at_0 D)

private theorem entry_5_0 (D : Adjoint.Space F) :
    entry D.val 5 0 = entry D.val 7 2 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_6_at_7 D)

private theorem entry_5_1 (D : Adjoint.Space F) :
    entry D.val 5 1 = entry D.val 7 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_4_at_5 D)

private theorem entry_5_2 (D : Adjoint.Space F) :
    entry D.val 5 2 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_2_at_1 D)

private theorem entry_5_3 (D : Adjoint.Space F) :
    entry D.val 5 3 = entry D.val 7 6 := by
  linear_combination (norm := ring_nf) (leibniz_0_6_at_3 D) + (leibniz_0_7_at_5 D) + (leibniz_1_2_at_1 D)

private theorem entry_5_4 (D : Adjoint.Space F) :
    entry D.val 5 4 = entry D.val 7 6 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_4_at_1 D) + (leibniz_0_6_at_3 D) + (leibniz_1_2_at_1 D)

private theorem entry_5_5 (D : Adjoint.Space F) :
    entry D.val 5 5 = entry D.val 6 6 + entry D.val 7 7 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_5_at_1 D) + (leibniz_0_6_at_2 D) + (leibniz_0_7_at_3 D) + (leibniz_1_2_at_0 D) + (leibniz_1_3_at_1 D)

private theorem entry_6_0 (D : Adjoint.Space F) :
    entry D.val 6 0 = entry D.val 7 1 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_5_at_7 D)

private theorem entry_6_1 (D : Adjoint.Space F) :
    entry D.val 6 1 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_1_0_at_2 D)

private theorem entry_6_2 (D : Adjoint.Space F) :
    entry D.val 6 2 = entry D.val 7 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_0_at_0 D) + (leibniz_0_2_at_2 D) + (leibniz_1_0_at_1 D) + (leibniz_1_4_at_5 D)

private theorem entry_6_3 (D : Adjoint.Space F) :
    entry D.val 6 3 = entry D.val 7 5 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_3_at_2 D) + (leibniz_0_5_at_3 D) + (leibniz_1_0_at_0 D)

private theorem entry_6_4 (D : Adjoint.Space F) :
    entry D.val 6 4 = entry D.val 7 5 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_1_at_0 D) + (leibniz_0_5_at_3 D) + (leibniz_1_0_at_0 D) + (leibniz_1_4_at_4 D)

private theorem entry_7_0 (D : Adjoint.Space F) :
    entry D.val 7 0 = 0 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_0_at_4 D)

private theorem entry_7_3 (D : Adjoint.Space F) :
    entry D.val 7 3 = entry D.val 7 4 := by
  have char_two : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (norm := (ring_nf; simp [char_two])) (leibniz_0_0_at_0 D) + (leibniz_0_7_at_7 D) + (leibniz_1_0_at_1 D) + (leibniz_1_4_at_5 D)

private theorem reconstruct_row_0 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 0 = entry D.val 0 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7]

private theorem reconstruct_row_1 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 1 = entry D.val 1 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_1_0, entry_1_1, entry_1_2, entry_1_3, entry_1_4, entry_1_5, entry_1_6]

private theorem reconstruct_row_2 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 2 = entry D.val 2 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_2_0, entry_2_1, entry_2_2, entry_2_3, entry_2_4, entry_2_5, entry_2_6]

private theorem reconstruct_row_3 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 3 = entry D.val 3 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_3_0, entry_3_1, entry_3_2, entry_3_3, entry_3_4, entry_3_5, entry_3_6, entry_3_7]

private theorem reconstruct_row_4 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 4 = entry D.val 4 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_4_0, entry_4_1, entry_4_2, entry_4_3, entry_4_4, entry_4_5, entry_4_6]

private theorem reconstruct_row_5 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 5 = entry D.val 5 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_5_0, entry_5_1, entry_5_2, entry_5_3, entry_5_4, entry_5_5]

private theorem reconstruct_row_6 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 6 = entry D.val 6 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_6_0, entry_6_1, entry_6_2, entry_6_3, entry_6_4]

private theorem reconstruct_row_7 (D : Adjoint.Space F) (j : Fin 8) :
    endomorphism (params F D) (basisVector j) 7 = entry D.val 7 j := by
  fin_cases j <;>
    simp [endomorphism, params, basisVector, entry_7_0, entry_7_3]

variable (F)

/-- Reconstruct a derivation from the fourteen independent entries. -/
@[simp] theorem fromParams_params (D : Adjoint.Space F) : fromParams F (params F D) = D := by
  apply Subtype.ext
  change endomorphism (params F D) = D.val
  apply Atlas.SplitOctonion.linearMap_ext
  intro j
  ext i
  fin_cases i
  · exact reconstruct_row_0 D j
  · exact reconstruct_row_1 D j
  · exact reconstruct_row_2 D j
  · exact reconstruct_row_3 D j
  · exact reconstruct_row_4 D j
  · exact reconstruct_row_5 D j
  · exact reconstruct_row_6 D j
  · exact reconstruct_row_7 D j

/-- A specified linear equivalence from actual derivations to fourteen coordinates. -/
def equiv : Adjoint.Space F ≃ₗ[F] Space F :=
  LinearEquiv.ofLinearMap (params F) (fromParams F)
    (LinearMap.ext (params_fromParams F))
    (LinearMap.ext (fromParams_params F))

@[simp] theorem equiv_apply (D : Adjoint.Space F) : equiv F D = params F D := rfl

@[simp] theorem equiv_symm_apply (r : Space F) : (equiv F).symm r = fromParams F r := rfl

/-- The actual octonion derivation space has dimension fourteen. -/
theorem finrank : Module.finrank F (Adjoint.Space F) = 14 := by
  simpa using (equiv F).finrank_eq

/-- Transport of the actual octonion automorphism group's adjoint action. -/
def action : Representation F (Model F) (Space F) :=
  (LinearEquiv.conjAlgEquiv F (equiv F)).toMonoidHom.comp (Adjoint.action F)

/-- The coordinate equivalence intertwines actual conjugation. -/
def repEquiv : Representation.RepEquiv (Adjoint.action F) (action F) where
  toLinearEquiv := equiv F
  isIntertwining' g := by
    apply LinearMap.ext
    intro D
    change equiv F (Adjoint.action F g D) =
      equiv F (Adjoint.action F g ((equiv F).symm (equiv F D)))
    rw [LinearEquiv.symm_apply_apply]

/-- A computation rule retaining conjugation of genuine derivations. -/
theorem action_apply (g : Model F) (r : Space F) :
    action F g r = params F (Adjoint.action F g (fromParams F r)) := rfl

end Atlas.G2.Restricted.Adjoint.Coordinates
