module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.Configuration
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension

/-!
# Terminal marked exclusions

The two S₄ locals in F.6.18(6) contradict the strict local-core inequality,
under either compatible generator labeling. This handles the marked L₃(2),
A₆ and source Â₆ alternatives without replacing the covering group or
either local embedding. The source configuration also forces the actual
module V₀ to have dimension greater than four. In the A₇ case the full
FF classification instead gives dimension four on V₀ itself, after
identifying the offender actor and removing the central quotient. This
excludes A₇ independently of which local group is labeled first.

The final theorem combines these exclusions on the literal quotient
images. The F.6.18/B.5.6 intersection supplies its marked alternatives;
proving that intersection and constructing the full classification
witnesses remain with the terminal case assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.309–310 and 1154–1155; B.4.2(7) and B.5.1, pp.86 and 99.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination

open ExceptionalAction.ActionRecognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)

/-- Apply the S₄ obstruction directly to the first local image occurring
in F.6.18. No choice of a different ambient model is needed. -/
theorem source_symmetricFour_quotient_excluded
    (localEquiv : d.G1.map (coreProjection (H := H)) ≃* Equiv.Perm (Fin 4)) : False := by
  apply source_symmetricFour_excluded d (MulEquiv.refl (coreQuotient H))
  exact localEquiv

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- Exclude A₇ using the full classification of the actual offender action.
Both local labelings are covered; dimension four and the identification
of the offender actor with the quotient are derived, not assumed. -/
theorem source_alternatingSeven_excluded
    (e : coreQuotient H ≃* alternatingGroup (Fin 7))
    (classification : SourceAlternative d.offenderAction) : False :=
  source_fourDimensional_excluded d (source_alternatingSeven_dimension d e classification)

/-- The marked alternatives eliminated on p.1155: the two S₄ locals of
F.6.18(6), including L₃(2), A₆ and Â₆, or an actual A₇ quotient.
The first clause is unchanged by interchanging the local labels. -/
theorem source_marked_cases_excluded
    (classification : SourceAlternative d.offenderAction)
    (alternatives :
      (Nonempty (d.G1.map (coreProjection (H := H)) ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty (d.G2.map (coreProjection (H := H)) ≃* Equiv.Perm (Fin 4))) ∨
      Nonempty (coreQuotient H ≃* alternatingGroup (Fin 7))) : False := by
  rcases alternatives with h | h
  · exact source_symmetricFour_quotient_excluded d h.1.some
  · exact source_alternatingSeven_excluded d h.some classification

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination
