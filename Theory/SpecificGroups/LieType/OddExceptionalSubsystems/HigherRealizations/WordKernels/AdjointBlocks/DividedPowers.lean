module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Integral

/-!
# Integral divided powers and specialization of the adjoint block

Intertwining of the integral simple operators implies intertwining of all their
powers. Their factorial identities then give the same statement for divided
powers, by cancelling a nonzero integer entrywise over ℤ. Only after this
cancellation do we extend scalars and form the signed polynomial root curves.
Thus the argument works over every commutative coefficient ring, including
characteristic three; it does not cancel any scalar in that coefficient ring.

Source: the common integral lattice in GLS3 §2.6.2 and the integral Geck
construction (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false
namespace TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
open Matrix RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq

section Matrices
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem pow_intertwines (A : Matrix m m ℤ) (B : Matrix n n ℤ)
    (J : Matrix n m ℤ) (h : B * J = J * A) (a : ℕ) :
    B ^ a * J = J * A ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', pow_succ', Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc, h, Matrix.mul_assoc]

/-- Cancellation takes place over the torsion-free integral lattice, before specialization. -/
theorem dividedPower_intertwines (A : Matrix m m ℤ) (B : Matrix n n ℤ)
    (J : Matrix n m ℤ) (h : B * J = J * A) (a : ℕ)
    (DA : Matrix m m ℤ) (DB : Matrix n n ℤ)
    (ha : A ^ a = a.factorial • DA) (hb : B ^ a = a.factorial • DB) :
    DB * J = J * DA := by
  have hh := pow_intertwines A B J h a
  rw [ha, hb] at hh
  simp only [Matrix.smul_mul, Matrix.mul_smul] at hh
  ext i j
  exact nsmul_right_injective (Nat.factorial_ne_zero a) (congrFun (congrFun hh i) j)
end Matrices

section RootSystems
variable {ι κ R M N M' N' : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {P : RootPairing ι R M N} {Q : RootPairing κ R M' N'}
  [P.IsCrystallographic] [P.IsReduced] [Q.IsCrystallographic] [Q.IsReduced]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {b : P.Base} {c : Q.Base}

namespace BasedEmbedding
variable (d : BasedEmbedding b c)

theorem eDividedPower_intertwines (i : b.support) (a : ℕ) :
    eDividedPower (d.base i) a * inclusion d.indexMap =
      inclusion d.indexMap * eDividedPower i a :=
  dividedPower_intertwines _ _ _ (d.eMatrix_intertwines i) a _ _
    (eMatrix_pow_eq_factorial_smul i a) (eMatrix_pow_eq_factorial_smul (d.base i) a)

theorem fDividedPower_intertwines (i : b.support) (a : ℕ) :
    fDividedPower (d.base i) a * inclusion d.indexMap =
      inclusion d.indexMap * fDividedPower i a :=
  dividedPower_intertwines _ _ _ (d.fMatrix_intertwines i) a _ _
    (fMatrix_pow_eq_factorial_smul i a) (fMatrix_pow_eq_factorial_smul (d.base i) a)

theorem coefficient_intertwines (S : Type*) [CommRing S]
    (s : Bool) (i : b.support) (a : ℕ) :
    (simpleFamily (b := c)).coefficient (s, d.base i) a * inclusionOver d.indexMap S =
      inclusionOver d.indexMap S * (simpleFamily (b := b)).coefficient (s, i) a := by
  have hh : (simpleFamily (b := c)).dividedPower (s, d.base i) a * inclusion d.indexMap =
      inclusion d.indexMap * (simpleFamily (b := b)).dividedPower (s, i) a := by
    cases s
    · exact d.fDividedPower_intertwines i a
    · exact d.eDividedPower_intertwines i a
  simpa only [Matrix.map_mul, IntegralCubicFamily.coefficient, inclusionOver] using
    congrArg (fun A => A.map (Int.castRingHom S)) hh

/-- Both signed polynomial curves commute with the inclusion over every commutative ring. -/
theorem curve_intertwines (S : Type*) [CommRing S]
    (s : Bool) (i : b.support) (t : S) :
    (simpleFamily (b := c)).curve (s, d.base i) t * inclusionOver d.indexMap S =
      inclusionOver d.indexMap S * (simpleFamily (b := b)).curve (s, i) t := by
  simp only [IntegralCubicFamily.curve, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    d.coefficient_intertwines]

end BasedEmbedding
end RootSystems
end TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
