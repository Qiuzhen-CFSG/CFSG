module
public import Theory.Representation.EssentialResidualQuotient
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceChiefLayer

/-!
# The essential residual quotient of the original qrc module

The original QRC span is elementary from its inside-core and ratio-two inputs.
Its two-residual acts nontrivially by the source no-common-normal argument.
Apply the essential quotient construction to this literal conjugation action:
the residual-moved image is irreducible, is contained in every nonzero
subrepresentation, and contains the fixed space of every Sylow two-subgroup.
The quotient itself has no residual-fixed vectors.

This is the quotient and fixed-socle step in Aschbacher–Smith3.1.9(5),
printed p.578, used by15.1.12(3). The earlier chosen-module placement and
ratio inputs remain explicit for their source producers; no natural-module
or chief-action classification is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open Representation.EssentialResidualQuotient
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The source quotient is formed from the original elementary conjugate span,
with residual nontriviality proved from QRC rather than assumed. -/
theorem QrcHypotheses.sqtk_essential_residual_quotient
    (h : QrcHypotheses T M M₀ H V)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    let ρ := normalRepresentation U
    ∃ W : Subrepresentation ρ,
      ¬ moved ρ (pResidual 2 H) ≤ W ∧
      (∀ N : Subrepresentation ρ, W < N → moved ρ (pResidual 2 H) ≤ N) ∧
      IsIrreducible (W.quotientImage (moved ρ (pResidual 2 H))).toRepresentation ∧
      (∀ N : Subrepresentation W.quotientRepresentation, N ≠ ⊥ →
        W.quotientImage (moved ρ (pResidual 2 H)) ≤ N) ∧
      fixedSpace W.quotientRepresentation (pResidual 2 H) = ⊥ ∧
      (∀ S : Sylow 2 H, fixedSpace W.quotientRepresentation S ≤
        (W.quotientImage (moved ρ (pResidual 2 H))).toSubmodule) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := (span_le_right_core d hV).trans (twoCore_le H)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  apply exists_residual_quotient (normalRepresentation U)
  apply moved_ne_bot_of_not_le_ker
  rw [MultipleFactors.normalRepresentation_ker]
  intro hh
  have hu : conjugateSpan H V ≤ centralizer ((pResidual 2 H).map H.subtype : Set G) := by
    intro u hu k hk
    obtain ⟨k,hk,rfl⟩ := hk
    exact congrArg H.subtype ((hh hk) ⟨u,hUH hu⟩ hu).symm
  exact residual_commutator_ne_bot d hne (commutator_eq_bot_iff_le_centralizer.mpr hu)

end CFSG.Quasithin.Chapter3
