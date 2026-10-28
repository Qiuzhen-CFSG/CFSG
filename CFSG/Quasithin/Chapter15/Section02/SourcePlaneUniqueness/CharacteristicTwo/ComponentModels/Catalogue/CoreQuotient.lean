module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.MSPreparation
public import Theory.SpecificGroups.SL3.PerfectCentralCover

/-!
# The full linear-three core quotient on the original component

The source kernel bound makes the literal map X/O₂(X) → X* a central
cover. The full SL₃ star model and trivial two-core force this map to be
injective, including at field orders two and four. Recognition therefore
preserves the specified star marking on every element of X. In particular
it identifies the full core quotient, not only its quotient by the center.

The actual NI odd-index witness and characteristic-normalizer control
then give all MS conditions on the original XR and R. C.1.34's module
classification remains a separate source theorem.

Source: Aschbacher--Smith C.2.7(g), printed pp.145--147, and original
15.2.23, printed pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

private noncomputable def linearThreeCover
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {F : Type*} [Field F] [Finite F] (e : starImage X R X ≃* SL(3,F)) :
    Cover (X ⧸ pCore 2 X) SL(3,F) where
  toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h

/-- The original star identification lifts to the entire core quotient. -/
noncomputable def linearThreeCoreEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {F : Type*} [Field F] [Finite F] (e : starImage X R X ≃* SL(3,F)) :
    (X ⧸ pCore 2 X) ≃* SL(3,F) := by
  let := h.quasisimple
  exact Matrix.SL3.centralCoverEquiv (linearThreeCover h e) (pCore_quotient_pCore_eq_bot 2)

/-- The full-quotient recognition agrees with the original map to the star group. -/
theorem linearThreeCoreEquiv_apply
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {F : Type*} [Field F] [Finite F] (e : starImage X R X ≃* SL(3,F))
    (x : X ⧸ pCore 2 X) :
    linearThreeCoreEquiv h e x = e (coreToStar h.normalizes x) := by
  let := h.quasisimple
  unfold linearThreeCoreEquiv
  exact Matrix.SL3.centralCoverEquiv_apply _ _ x

/-- In a full linear-three star row, the comparison kernel is trivial. -/
theorem linearThree_coreToStar_injective
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {F : Type*} [Field F] [Finite F] (e : starImage X R X ≃* SL(3,F)) :
    Function.Injective (coreToStar h.normalizes) := by
  intro x y hxy
  apply (linearThreeCoreEquiv h e).injective
  simpa only [linearThreeCoreEquiv_apply] using congrArg e hxy

/-- Recognition also retains the literal projection from each element of X. -/
theorem linearThreeCoreEquiv_mk
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {F : Type*} [Field F] [Finite F] (e : starImage X R X ≃* SL(3,F)) (x : X) :
    linearThreeCoreEquiv h e (QuotientGroup.mk' (pCore 2 X) x) =
      e (toStarImage X R x) := by
  rw [linearThreeCoreEquiv_apply, coreToStar_mk]

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- The full core-quotient premise in MS preparation is now discharged on
exactly the selected X, R = O₂(NI), and NI = M intersect I. -/
theorem normalized_component_msPair_of_star_model
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(3,F)) :
    LinearThreeMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F := by
  exact normalized_component_msPair_of_core_model d hI hcore s n F hn hF
    (linearThreeCoreEquiv (normalized_component_input (hsource := hsource) hI hcore s) e)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
