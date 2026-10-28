module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange.Transport
public import Theory.Representation.OrthogonalFourPlusMatrix.PrimeFieldTwo.FactorNormalizer

/-!
# Concrete factor interchange for the literal Chapter 15 action

The fixed binary determinant-action normalizer theorem discharges the
independent matrix-model premise of `factorExchange_of_normalizer_exchange`.
The existing transport retains the actual natural action, intrinsic quotient,
ordered factor preimages, and the source's inverse-conjugation convention.
Only the order of the natural T-image remains as an input; the Chapter 15
assembly supplies that order from its earlier action and Sylow hypotheses.

Source: Aschbacher–Smith, G.2.6(5), printed p.336, and the Chapter 15
application on printed pp.1121–1122 and 1146–1147.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Order eight for the literal natural action forces interchange of the marked factors. -/
theorem factorExchange_of_natural_image_card (d : Hypothesis D g)
    (hcard : Nat.card (D.VL.normalizerMonoidHom.comp
      (inclusion (Chapter15Collapse.T_normalizes_natural d))).range = 8) :
    FactorExchange d := by
  apply factorExchange_of_normalizer_exchange d _ hcard
  intro P hP horder
  exact ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo.FactorNormalizer.exists_exchange
    P hP horder

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
