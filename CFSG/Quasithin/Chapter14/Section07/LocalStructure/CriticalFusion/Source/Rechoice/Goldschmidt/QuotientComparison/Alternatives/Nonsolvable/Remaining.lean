module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Component

/-!
# Remaining finite models in the subnormal comparison

These are actual F.6.18 models, with their original isomorphisms and cover
records. The component order comparison for this finite family and the
separate product/outer-action argument are independent prerequisites of
14.7.70; this definition asserts neither exclusion nor recognition.

Source: Aschbacher–Smith, F.6.18(7)–(9),(12), printed pp.309–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- Every model is attached to the actual ambient group. -/
def ExceptionalModel (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ FSource.TripleAlternating D 7 ∨
  Nonempty (FSource.TripleSymmetric D 6) ∨ Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨
  Nonempty (FSource.TripleSymmetric D 7) ∨ Nonempty (D ≃* Sporadic.Mathieu.M12)

/-- The two outstanding families after the classical-component comparison. -/
def UnresolvedRow {D : Type*} [Group D] [Finite D] (S : Sylow 2 D) : Prop :=
  (Nonempty (FSource.ProductRow S) ∧ Nat.card S = 8) ∨
    (IsQuasisimple (generalizedFitting D) ∧ ExceptionalModel D)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
