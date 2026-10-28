module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductAssembly
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalModule
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductCentralizer

/-!
# TerminalProductAssembly at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductAssembly`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

theorem productAnalysis_of_marked_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  obtain ⟨F⟩ := P.localFactorAnalysis_at structural escape C
  exact ⟨{
    reduced := P.U_reduced
    centralizer_eq := P.U_centralizer_eq_twoCore_at structural escape C
    quotient := q
    first_image := hfirst
    second_image := hsecond
    thompson_image := hthompson
    second_quotient := F.second_quotient
    second_natural := F.second_natural
    weight_two := F.weight_two }⟩

theorem false_of_marked_product_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  obtain ⟨A⟩ := P.productAnalysis_of_marked_quotient_at structural escape C q hfirst hsecond hthompson
  exact P.false_of_module_analysis_at structural A

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

