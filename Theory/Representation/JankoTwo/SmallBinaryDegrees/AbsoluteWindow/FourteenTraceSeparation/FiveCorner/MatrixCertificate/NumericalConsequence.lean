module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Checks0
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Checks1
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Checks2
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.Checks3
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.AllowedTables

/-!
# Consequence of the numeral-form matrix relations

The checked pair evaluations restrict each pair to its allowed table. Five
potentially noncommuting pairs are eliminated by an explicit third generator;
all other pairs commute already. This proves the full nine-generator statement
for `numericalRelations`, without enumeration of all nine-tuples.

Identification with the shared string-decoded relations is kept explicit in
the final `MatrixCertificate.lean` assembly.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
open Certificate

theorem forbidden_eq (i j : Fin 9) (hij : i < j) :
    forbidden numericalRelations i j = mask ^^^ allowedMask i j := by
  fin_cases i <;> fin_cases j
  · exact ((by decide : ¬ ((0 : Fin 9) < 0)) hij).elim
  · exact checks0.1
  · exact checks0.2.1
  · exact checks0.2.2.1
  · exact checks0.2.2.2.1
  · exact checks0.2.2.2.2.1
  · exact checks0.2.2.2.2.2.1
  · exact checks0.2.2.2.2.2.2.1
  · exact checks0.2.2.2.2.2.2.2.1
  · exact ((by decide : ¬ ((1 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((1 : Fin 9) < 1)) hij).elim
  · exact checks0.2.2.2.2.2.2.2.2
  · exact checks1.1
  · exact checks1.2.1
  · exact checks1.2.2.1
  · exact checks1.2.2.2.1
  · exact checks1.2.2.2.2.1
  · exact checks1.2.2.2.2.2.1
  · exact ((by decide : ¬ ((2 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((2 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((2 : Fin 9) < 2)) hij).elim
  · exact checks1.2.2.2.2.2.2.1
  · exact checks1.2.2.2.2.2.2.2.1
  · exact checks1.2.2.2.2.2.2.2.2
  · exact checks2.1
  · exact checks2.2.1
  · exact checks2.2.2.1
  · exact ((by decide : ¬ ((3 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((3 : Fin 9) < 3)) hij).elim
  · exact checks2.2.2.2.1
  · exact checks2.2.2.2.2.1
  · exact checks2.2.2.2.2.2.1
  · exact checks2.2.2.2.2.2.2.1
  · exact checks2.2.2.2.2.2.2.2.1
  · exact ((by decide : ¬ ((4 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 9) < 3)) hij).elim
  · exact ((by decide : ¬ ((4 : Fin 9) < 4)) hij).elim
  · exact checks2.2.2.2.2.2.2.2.2
  · exact checks3.1
  · exact checks3.2.1
  · exact checks3.2.2.1
  · exact ((by decide : ¬ ((5 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 9) < 3)) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 9) < 4)) hij).elim
  · exact ((by decide : ¬ ((5 : Fin 9) < 5)) hij).elim
  · exact checks3.2.2.2.1
  · exact checks3.2.2.2.2.1
  · exact checks3.2.2.2.2.2.1
  · exact ((by decide : ¬ ((6 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 3)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 4)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 5)) hij).elim
  · exact ((by decide : ¬ ((6 : Fin 9) < 6)) hij).elim
  · exact checks3.2.2.2.2.2.2.1
  · exact checks3.2.2.2.2.2.2.2.1
  · exact ((by decide : ¬ ((7 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 3)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 4)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 5)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 6)) hij).elim
  · exact ((by decide : ¬ ((7 : Fin 9) < 7)) hij).elim
  · exact checks3.2.2.2.2.2.2.2.2
  · exact ((by decide : ¬ ((8 : Fin 9) < 0)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 1)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 2)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 3)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 4)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 5)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 6)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 7)) hij).elim
  · exact ((by decide : ¬ ((8 : Fin 9) < 8)) hij).elim

private theorem mask_bit : ∀ p : Fin 256, mask.testBit p.val = true := by
  decide +kernel

theorem allowed_of_forbidden (i j : Fin 9) (a b : Fin 16)
    (h : (mask ^^^ allowedMask i j).testBit (16 * a.val + b.val) = false) :
    allowed i j a b = true := by
  have hp : 16 * a.val + b.val < 256 := by have := a.isLt; have := b.isLt; omega
  rw [Nat.testBit_xor, mask_bit ⟨_, hp⟩] at h
  cases hb : (allowedMask i j).testBit (16 * a.val + b.val) <;>
    simp_all [allowed]

theorem numerical_allowed (x : Fin 9 → Fin 16)
    (h : ∀ r ∈ numericalRelations, r.value (fun i => decode (x i)) = 0) :
    ∀ i j, allowed i j (x i) (x j) = true := by
  have hlt (i j : Fin 9) (hij : i < j) : allowed i j (x i) (x j) = true := by
    apply allowed_of_forbidden
    rw [← forbidden_eq i j hij]
    exact forbidden_false numericalRelations x h i j
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · subst j; exact allowed_self i (x i)
  · rw [allowed_symm]; exact hlt j i hij

/-- The complete finite-matrix implication for the numeral-form relations. -/
theorem numerical_commutativity
    (x : Fin 9 → Matrix (Fin 2) (Fin 2) (ZMod 2))
    (h : ∀ r ∈ numericalRelations, r.value x = 0) (i j : Fin 9) :
    x i * x j = x j * x i := by
  choose c hc using fun k => decode_surjective (x k)
  have hdecode : (fun k => decode (c k)) = x := funext hc
  have hn : ∀ r ∈ numericalRelations, r.value (fun k => decode (c k)) = 0 := by
    simpa only [hdecode] using h
  simpa only [hc] using commute_of_allowed c (numerical_allowed c hn) i j

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
