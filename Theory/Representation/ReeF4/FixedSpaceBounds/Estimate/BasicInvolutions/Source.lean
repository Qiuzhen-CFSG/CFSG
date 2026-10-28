module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.SourcePlacement
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Spectrum

/-!
# The source involution bound on every exceptional basic factor

Actual order-five/order-thirteen torus placement combines with the proved
short/long weight balance and finite character count. Every relevant odd
actor therefore moves at least twenty dimensions on each nontrivial basic
factor. The actual involution inversion witnesses and the commutator rank
inequality give the ten-dimensional bound on every exceptional twist.

This completes the local basic-factor estimate. Finite irreducible tensor
realization and its Frobenius period remain separate source representation
theorems in the final binary and central-cover assembly.

Source: Guralnick–Malle, *Classification of 2F-modules II*, Lemma 8.8,
internal pp.57–58; GLS3 §§1.14, 2.8.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions
open Theory.AlgebraicGroup Representation Subgroup
open ReeF4.BinaryDegree.ExceptionalTensor BinaryOddElements
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Literal torus coordinates with at least twenty moving end-node weights. -/
theorem binaryOddTorusCoverage : BinaryOddTorusCoverage F :=
  TorusCoverage.coverage_of_placement_balance_spectrum (TorusCoverage.placement F)
    TorusCoverage.Balance.balance (TorusCoverage.primeSpectrumBound F)

/-- The actual order-five/order-thirteen action on every large basic factor. -/
theorem binaryOddDisplacement : BinaryOddDisplacement F :=
  binaryOddDisplacement_of_torusCoverage binaryOddTorusCoverage

/-- Every nonidentity involution moves at least ten dimensions on the
specified exceptional basic factor, with the original coefficient embedding. -/
theorem basic_involution_bound {m : ℕ} (hm : 1 ≤ m)
    (f : CoefficientField m →+* F) (B : AlgebraicFactor F)
    (hB : B.IsExceptionalBasic) (hdim : 26 ≤ Module.finrank F B.Space)
    (i : ZMod (2 * m + 1)) (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp
        ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ.comp
          (zpowers t).subtype)) :=
  basic_involution_bound_of_binary_odd_bounds (InversionCoverage.binaryOddInversionCoverage m hm)
    binaryOddDisplacement f B hB hdim i t ht ht2

/-- The literal factor used by the tensor estimate has the same proved bound. -/
theorem exceptionalFactor_involution_bound {m : ℕ} (hm : 1 ≤ m)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic) (i : ZMod (2 * m + 1))
    (hdim : 26 ≤ Module.finrank F (B i).Space)
    (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 ≤ Module.finrank F
      ((exceptionalFactor (Classification.splitEmbedding (Classification.coefficientHom F m)) B i) ⧸
        invariants ((exceptionalFactor
          (Classification.splitEmbedding (Classification.coefficientHom F m)) B i).ρ.comp
            (zpowers t).subtype)) :=
  exceptionalFactor_involution_bound_of_binary_odd_bounds (InversionCoverage.binaryOddInversionCoverage m hm)
    binaryOddDisplacement B hB i hdim t ht ht2

end ReeF4.FixedSpaceEstimate.BasicInvolutions
