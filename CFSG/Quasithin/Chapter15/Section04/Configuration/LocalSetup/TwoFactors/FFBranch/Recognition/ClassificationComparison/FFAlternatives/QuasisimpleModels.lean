module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.G2Natural

/-!
# The generalized-Fitting models in B.5.6(1)

Every alternative specifies an actual multiplicative equivalence. The
exceptional triple cover uses the source convention: a quasisimple group
with cyclic center of order three and central quotient A₆. Both central
identifications are actual isomorphisms. Quasisimplicity itself is a separate
source conclusion, so it can be reused when proving model facts.

The binary projective linear groups are represented by their special linear
models, whose scalar centers are trivial. The distinction between the full
G₂(2) and its commutator subgroup is retained. This is only the group list;
the full B.5.1 module conclusions must accompany it in B.5.6(1).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(1),
printed p.105, with the cover convention A.3.5.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u

/-- The complete ten-model list for the quasisimple generalized Fitting
subgroup. No assertion about its three-prime core is built into the list. -/
inductive QuasisimpleModel (L : Type u) [Group L] : Prop
  | linearTwo (F : BinaryField)
      (equiv : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | linearThree (F : BinaryField)
      (equiv : L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
  | symplecticFour (F : BinaryField)
      (equiv : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (equiv : L ≃* Atlas.G2.Model F.Carrier)
  | alternatingSix (equiv : L ≃* alternatingGroup (Fin 6))
  | alternatingSeven (equiv : L ≃* alternatingGroup (Fin 7))
  | tripleSix (centerEquiv : center L ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
  | g2DerivedTwo (equiv : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | linearFourTwo (equiv : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  | linearFiveTwo (equiv : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
