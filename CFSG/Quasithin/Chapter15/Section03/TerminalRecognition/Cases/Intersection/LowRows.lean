module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Actors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Models
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Extraspecial
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct

/-!
# Terminal low-row comparison

When the ambient generalized Fitting subgroup is not quasisimple, the
exhaustive F.6.18 reduction leaves the S₃ × S₃ row, an extraspecial
extension, or the PSL₂(p) × C₃ residual row. The first has Thompson image
S₃; comparison with the full B.5.6 alternatives on the original offender
action excludes the other two. Both local labelings are allowed, with the
source's actual subgroup embeddings, quotient maps and outer actions.

This completes the nonquasisimple ambient branch of the conditional
intersection. The parent supplies the two classification witnesses and
assembles the remaining quasisimple ambient branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; F.6.16–18, pp.308–310; B.5.1/B.5.6, pp.99–105.
-/

public section
open Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The full classification witnesses identify the actual Thompson image
with S₃ when the ambient generalized Fitting subgroup is not quasisimple.
The Goldschmidt witness may use either labeling of the original local groups. -/
theorem thompson_symmetricThree_of_nonquasisimple
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection) d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection) d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction)
    (hnot : ¬ IsQuasisimple (generalizedFitting (coreQuotient H))) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) := by
  rcases d.symmetricThree_or_product_low_row_of_sourceAlternative hF hnot hB with
    he | ⟨c, hs, hl⟩
  · exact he
  · exact d.thompson_symmetricThree_of_primeProduct c hs hl hB

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
