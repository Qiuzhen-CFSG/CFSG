module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Core
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Rows
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The orthogonal-six row supplies a genuine FF* offender

The marked alternating-eight action on U/C_U(X) is faithful. Hence the
original action of X/O₂(X) on U is faithful as well. The core and Thompson
argument then constructs a best offender in the actual QI-action on U.
The subsequent marked-parabolic exclusion is a separate required step.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117, and B.3.2(6).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource

/-- A faithful alternating-eight quotient forces faithfulness of the original action. -/
theorem faithful_of_orthogonalSix_quotient
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (C : Subrepresentation ρ)
    (e : ActionEquiv C.quotientRepresentation (alternatingNatural 8)) :
    Function.Injective ρ := by
  intro g h he
  apply e.groupEquiv.injective
  apply (BinaryPermutation.naturalRepresentation_injective (Fin 8) (by decide)).comp
    (alternatingGroup (Fin 8)).subtype_injective
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  change alternatingNatural 8 (e.groupEquiv g) (e.linearEquiv w) =
    alternatingNatural 8 (e.groupEquiv h) (e.linearEquiv w)
  rw [← e.intertwines, ← e.intertwines]
  apply congrArg e.linearEquiv
  induction w using Submodule.Quotient.induction_on with
  | _ w =>
    exact congrArg C.toSubmodule.mkQ (LinearMap.congr_fun he w)

/-- The orthogonal module data constructs the FF* witness; neither the
marked core identity nor the existence of an offender is an input. -/
theorem U_bestOffender_of_orthogonalSix
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      ActionEquiv C.quotientRepresentation (alternatingNatural 8) →
      let E := X ⊔ QI H T ZS
      let W := (U X ZS).subgroupOf E
      let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
      let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
          ((U_le_QI d hI hfit hXI).trans le_sup_right)
      let q := QuotientGroup.mk' (centralizer (W : Set E))
      ∃ A ∈ elementaryAbelianMaxSubgroups ((QI H T ZS).subgroupOf E),
        Representation.BinaryOffender.IsBestOffender
          (Representation.NormalElementaryQuotient.representation W q
            (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  let := U_elementary d hI hfit hXI
  intro C e
  exact U_bestOffender_of_faithful d hI hfit hXI hn hout hKX
    (faithful_of_orthogonalSix_quotient C e)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
