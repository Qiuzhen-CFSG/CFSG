module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductCentralizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalModule

/-!
# Terminal product assembly from the remaining marked quotient

The local factors, their natural action, the weight-two seed, reducedness
and the full centralizer kernel are supplied by proved source calculations.
This assembly retains only the marked S₅×S₃ quotient and its full Thompson
image. Those remaining hypotheses belong to qt-d-1231-terminal-product;
this conditional application is not the construction of ProductAnalysis.
ComponentAnalysis is discharged by qt-d-1231-terminal.

The second theorem feeds the literal B.5.6 module application and terminal
contradiction, preserving every original quotient map and factor image.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The exact remaining quotient obligations suffice for all ProductAnalysis
fields. Their construction remains with the product owner. -/
theorem productAnalysis_of_marked_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : (P.Y ⧸ pCore 2 P.Y) ≃* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)))
    (hfirst : (P.K.subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
        (alternatingGroup (Fin 5)).prod ⊥)
    (hsecond : (P.L2.subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
        (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)))
    (hthompson : ((Stellmacher.elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) = ⊤) :
    Nonempty P.ProductAnalysis := by
  obtain ⟨F⟩ := P.localFactorAnalysis structural escape C
  exact ⟨{
    reduced := P.U_reduced
    centralizer_eq := P.U_centralizer_eq_twoCore structural escape C
    quotient := q
    first_image := hfirst
    second_image := hsecond
    thompson_image := hthompson
    second_quotient := F.second_quotient
    second_natural := F.second_natural
    weight_two := F.weight_two }⟩

/-- Actual B.5.6 and terminal consumer application of the source calculations.
The marked quotient and full Thompson image remain explicit obligations. -/
theorem false_of_marked_product_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : (P.Y ⧸ pCore 2 P.Y) ≃* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)))
    (hfirst : (P.K.subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
        (alternatingGroup (Fin 5)).prod ⊥)
    (hsecond : (P.L2.subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
        (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)))
    (hthompson : ((Stellmacher.elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) = ⊤) : False := by
  obtain ⟨A⟩ := P.productAnalysis_of_marked_quotient structural escape C q hfirst hsecond hthompson
  exact P.false_of_module_analysis structural A

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
