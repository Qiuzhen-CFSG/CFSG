module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.FFSpectrum

/-!
# Prime-product branch of the terminal intersection

The actual PSL₂(p) factor lies inside the Thompson image and hence inside
the original offender subgroup. Its defining prime p ≥ 11 divides that
subgroup's order, while sixteen does not. The complete supplied B.5.6
alternatives bound every prime divisor of the same offender subgroup by
seven, so the prime-product row is impossible.

The exclusion applies to both local labelings and retains the entire
product witness, including the ambient residual and actual outer actions.
The concluding adapter matches the product constructor of `RemainingRow`.
No equality between the offender actor and the ambient quotient, or bound
on ambient three-rank, is needed. The universal classifications remain
with their source owners; this module completes their row comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.6.18(3),
printed p.309, and its comparison with B.5.6 on printed p.1155.
-/

public section
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The complete FF alternatives on the original offender action exclude
F.6.18(3), independently of the labeling of its two local groups. -/
theorem no_primeProduct_row_of_sourceAlternative
    (c : FSource.ProductRow d.quotientSylow)
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (hB : FFAlternatives.SourceAlternative d.offenderAction) : False :=
  d.no_primeProduct_row_of_offender_prime_bound c hs
    (d.primeProduct_offender_prime_le_seven hs hB)

/-- Discharge the product constructor of the terminal low-row reduction,
with both original local labelings and all product data retained. -/
theorem thompson_symmetricThree_of_primeProduct
    (c : FSource.ProductRow d.quotientSylow)
    (hs : Nonempty (d.quotientSylow ≃* DihedralGroup 4))
    (_locals :
      (Nonempty (d.G1.map coreProjection ≃* DihedralGroup 12) ∧
        Nonempty (d.G2.map coreProjection ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (d.G2.map coreProjection ≃* DihedralGroup 12) ∧
        Nonempty (d.G1.map coreProjection ≃* Equiv.Perm (Fin 4))))
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) :=
  (d.no_primeProduct_row_of_sourceAlternative c hs hB).elim

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
