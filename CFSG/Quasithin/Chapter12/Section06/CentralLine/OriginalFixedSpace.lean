module

public import CFSG.Quasithin.Chapter12.Section06.CentralLine.OriginalEscape
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.ChosenFiveSource
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates

/-!
# Original source 12.6.23 at the same ambient group and Sylow subgroup

The original orthogonal configuration excludes every global alternative
of the earlier recognition theorem by order divisibility. The resulting
uniform escape gives the earlier A₇ exclusion. One actual chosen summand
of the escaping H-star omega-span then supplies the five-point action
contradiction. Thus the original C_V(L) vanishes.

Only the original Section06 source hypothesis, same-G,T structural and
module statements of 12.2.2, and the multiple-overgroup guard are inputs.
The resulting full coordinates retain the original quotient projection
and marked action on the unchanged V. This proves 12.6.23, not the remaining
HS/J₄ nonsingular-centralizer cases of 12.6.2 or all of 12.6.34.

Source: Aschbacher–Smith, 12.6.23 and its following setup, pp.829–831.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Full original 12.6.23 with every earlier escape, A₇ and local action
premise discharged from the same ambient source prefix. -/
theorem SourceHypothesis.original_fixed_space_eq_bot
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ZV L V = ⊥ :=
  S.fixed_space_eq_bot_of_chosen_five_source D structural modules
    (S.original_not_alternating_seven D structural modules hmany)

/-- The unchanged original V has full six-dimensional equivariant
coordinates, with the original fixed-space quotient map recorded explicitly. -/
theorem SourceHypothesis.original_fixed_space_and_full_coordinates
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ZV L V = ⊥ ∧ Module.finrank (ZMod 2) (Additive V) = 6 ∧
      ∃ E : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
        (∀ v, E v = D.coordinates (Submodule.Quotient.mk v)) ∧
        ∀ (l : L) v, E (seedRepresentation L V S.chosen.normalizes l v) =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
            (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker l)) (E v) := by
  have hz := S.original_fixed_space_eq_bot D structural modules hmany
  let E := D.fullLinearCoordinates hz
  refine ⟨hz,E.finrank_eq.trans BinaryPermutation.TerminalOrthogonal.Eight.finrank_natural,
    E,D.fullLinearCoordinates_apply hz,?_⟩
  intro l v
  rw [D.fullLinearCoordinates_apply,D.fullLinearCoordinates_apply]
  exact D.equivariant l (Submodule.Quotient.mk v)

end CFSG.Quasithin.Chapter12.Section06
