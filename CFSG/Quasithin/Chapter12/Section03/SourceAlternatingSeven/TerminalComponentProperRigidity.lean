module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentBranches
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperCubics

/-!
# The proper-overcomponent rigidity contract

This file isolates the two source facts used in the proper branch of the
proof of 12.3.12.  The first is the restriction from A.3.14: with the
literal local membership and relative normality retained, a proper
intermediate component `K < E ≤ Y` is the maximal component `Y`.  The
second is the repaired last step.  It uses the actual containment
`L_e ≤ Y`, but does not identify `L_e` or its perfect residual with an
`A₅`; the source assembly supplies the resulting ambient uniqueness
conclusion directly.

The latter premise is necessary with the current notation.  The weight-four
stabilizer in the `A₇` quotient is solvable, so the printed assertion
`K = L_e^∞` is not a valid Lean consequence of `L_e ≤ Y`.

Source: Aschbacher--Smith A.3.14 and Lemma 12.3.12, printed pp.49--50 and
811; Notation 12.2.5(3), printed p.796.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u

variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable {P : TerminalPoint S D}

/--
The exact local and relative-normality interface for the A.3.14 restriction.

The fields carried by `F` are repeated as arguments deliberately: this keeps
the source theorem's hypotheses visible at the assembly boundary and prevents
an unrelated component or maximal local member from being substituted.
The restriction itself is the remaining A.3.14 source input.
-/
structure A314RestrictionInput where
  restrict : ∀ (F : P.Overcomponents),
    P.K < F.E →
    F.E ∈ Chapter1.cComponentsIn P.pointCentralizer →
    P.pointCentralizer ≤ normalizer (F.E : Set G) →
    F.E ∈ Chapter1.L G (T : Subgroup G) →
    F.E ≤ F.Y →
    F.Y ∈ Chapter1.LStar G (T : Subgroup G) →
    (∃ W : Subgroup G, Nonempty (Setup T F.Y W)) →
    F.E = F.Y

namespace A314RestrictionInput

/-- The A.3.14 restriction applied to an actual overcomponent. -/
theorem eq_maximal (A : A314RestrictionInput (P := P))
    (F : P.Overcomponents) (hKE : P.K < F.E)
    (hsetup : ∃ W : Subgroup G, Nonempty (Setup T F.Y W)) :
    F.E = F.Y :=
  A.restrict F hKE F.component F.normalizes F.local_mem F.le_maximal F.maximal hsetup

end A314RestrictionInput

/--
The repaired ambient uniqueness contract for the last paragraph of the
proper branch.  It is intentionally weaker than the invalid claim that
`P.Le` has an `A₅` perfect residual: once the actual `P.Le ≤ F.Y` has been
proved, it returns only the inclusion `P.K ≤ P.Le` needed for escape.

The `Setup` argument records that this is the genuine 12.3.7/12.2.8 branch,
rather than an unrelated subgroup of `F.Y`.
-/
def AmbientA5Uniqueness (F : P.Overcomponents) : Prop :=
  ∀ {W : Subgroup G}, Setup T F.Y W → F.E = F.Y → P.Le ≤ F.Y → P.K ≤ P.Le

/-- `Le = O²(L ∩ C_G(e))` is a subgroup of the original component `L`. -/
theorem Le_le_original : P.Le ≤ L := by
  change (pResidual 2 (L ⊓ P.pointCentralizer : Subgroup G)).map
      (L ⊓ P.pointCentralizer).subtype ≤ L
  exact (map_subtype_le _).trans inf_le_left

/--
The intermediate-component restriction is the proper branch of A.3.14,
with all local and relative-normality hypotheses supplied by `F`.
-/
theorem intermediate_component_eq_maximal
    (A : A314RestrictionInput (P := P)) (F : P.Overcomponents)
    (hKE : P.K < F.E)
    (hsetup : ∃ W : Subgroup G, Nonempty (Setup T F.Y W)) :
    F.E = F.Y :=
  A.eq_maximal F hKE hsetup

/-
The proper rigidity step is kept separate from A.3.14 so that its actual
consumer can discharge the repaired ambient uniqueness premise independently
of cubic generation.
-/
theorem proper_component_eq_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y)
    (hunique : AmbientA5Uniqueness (P := P) F) :
    F.E = P.K := by
  by_contra hne
  have hKE : P.K < F.E := lt_of_le_of_ne F.residual_le (Ne.symm hne)
  have hKYle : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  have hsetup : ∃ W' : Subgroup G, Nonempty (Setup T F.Y W') :=
    (R.overgroups F.Y F.maximal hKYle).2.resolve_left (ne_of_lt hKY)
  have hEY : F.E = F.Y := A.eq_maximal F hKE hsetup
  have hLeY : P.Le ≤ F.Y := hLe hEY
  have hKLe : P.K ≤ P.Le := hunique SY hEY hLeY
  exact P.residual_escape structural
    (hKLe.trans ((Le_le_original (P := P)).trans L.le_normalizer))

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
