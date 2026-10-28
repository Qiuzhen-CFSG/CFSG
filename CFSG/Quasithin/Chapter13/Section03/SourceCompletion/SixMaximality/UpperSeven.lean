module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.SevenExtension
public import Theory.Representation.BinaryAlternatingSevenSmallExtension

/-!
# The A₇ upper core and the original core are the natural module

The canonical upper action has dimension at most five, contains the
original irreducible A₆ four-space, and has no fixed vectors for that
lower image. The proved small A₇ extension theorem therefore gives
upper dimension four, identifying O₂(I) with the actual original V.
The existing cohomological centralizer argument then gives O₂(LT)=V.

This supplies the genuine source13.5.15(7) core equality in the remaining
A₇ upper branch without assuming maximality of L. It is the input to
the seven-free Gz calculation used to finish original13.3.2 in this
normal A₆ case. Source: Aschbacher–Smith I.1.6(8),13.3.2,13.5.15,
pp.408,884–885,920–921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- Apply the complete small-module theorem to the actual conjugation representation. -/
theorem upper_core_eq_module_of_seven {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    I.pCoreIn 2 = D.V := by
  obtain ⟨he,hc⟩ := UpperCore.upper_core_elementary_bound d h e hseed hn hU
    hI.maximal_faithful.1.1 hLI
  let : IsElementaryAbelian 2 (pCore 2 I) := he
  have hVW := module_le_upper_core d h e hseed hn hU hI hLI
  let U := lowerModule d hLI eI
  let : U.toRepresentation.IsIrreducible := lowerModule_irreducible d hLI eI hVW
  have hdim : Module.finrank (ZMod 2) (Additive (pCore 2 I)) ≤ 5 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    have hw := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (pCore 2 I))
    change Nat.card (pCore 2 I) = _ at hw
    rw [Nat.card_zmod] at hw
    rw [← hw]
    exact hc
  have hfour := Representation.BinaryAlternatingSevenSmallExtension.finrank_eq_four
    (coreSevenRepresentation eI) (lowerSevenMap hLI eI).range
    (lowerSevenMap_card e hLI eI) U (lowerModule_finrank d hLI eI hVW) hdim
    (coreSevenRepresentation_fixed_eq_bot d h e hseed hn hU hI hLI eI)
  have hcard : Nat.card (I.pCoreIn 2) = 16 := by
    have hw := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (pCore 2 I))
    change Nat.card (pCore 2 I) = _ at hw
    rw [Nat.card_zmod,hfour] at hw
    exact (card_map_of_injective I.subtype_injective).trans hw
  exact (eq_of_le_of_card_ge hVW (by rw [hcard,ReturningPlane.module_card d])).symm

/-- The A₇ upper branch forces the original source core equality. -/
theorem original_core_eq_module_of_seven {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    D.LT.pCoreIn 2 = D.V :=
  original_core_eq_module_of_seven_core d h e hseed hn hU hI hLI eI
    (upper_core_eq_module_of_seven d h e hseed hn hU hI hLI eI)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
