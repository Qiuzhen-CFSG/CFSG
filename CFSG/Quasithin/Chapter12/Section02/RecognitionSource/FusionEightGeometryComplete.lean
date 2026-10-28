module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModuleComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionMoved
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionPointGeometryFixedComparison
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryTerminal
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAssembly

/-!
# Completing the alternating-eight point-Sylow geometry

Under the original chosen-module, structural and NoEscape hypotheses, construct
the reduced FF-module on the literal L-conjugate span of Ω₁Z(C_T(v)). The moved
module theorem identifies its commutator with V. The proved comparison of the
point fixed spaces then supplies both the corrected fixed-core decomposition
and T-centralization of its supplement. The terminal intersection argument
gives Ω₁Z(C_T(v)) ≤ V, and the original fixed-line fusion theorem excludes
the marked outside conjugator. No additional geometric premise remains.

The final application discharges the alternating-eight input of
`globalTI_of_row_reductions`. Its independent fixed-free and reducible source
reductions remain explicit; their universal assembly belongs to the fusion
owner. This argument needs neither an exact dimension of the point-fixed core
nor the printed hyperplane assertion.

Source: Aschbacher--Smith, 12.2.16, final paragraph, printed p.800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightFusion
variable (C : AlternatingEightFusion T L V)

/-- The original hypotheses put the actual point-Sylow central omega inside V. -/
theorem omega_le_of_original_hypotheses
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V) :
    omegaCenterIn C.pointSylow ≤ V := by
  let R := C.pointSpanModule h D structural hnone
  have hm := C.pointSpan_commutator_eq_chosen h.toHypothesis1221 D R
  have hfixed := C.point_fixed_comparison h D structural hnone
  obtain ⟨hsplit, hT⟩ :=
    C.pointFixed_conclusions_of_moved_and_fixed_comparison h D structural hnone R hm.le hfixed
  exact C.omega_le_of_pointCore_decomposition h D structural hnone hsplit hT

include C in
/-- The completed geometry excludes the original marked A₈ fusion configuration. -/
theorem false_of_original_hypotheses
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V) :
    False := by
  exact C.false_of_omega_le h D structural hnone
    (C.omega_le_of_original_hypotheses h D structural hnone)

end AlternatingEightFusion

/-- The actual row-reduction consumer no longer needs an A₈ geometry callback. -/
theorem globalTI_of_row_reductions_of_eight_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V)
    (fixedFree : V ⊓ centralizer (L : Set G) = ⊥ → IsTISubgroup V)
    (reducible : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V)) :
    IsTISubgroup V :=
  globalTI_of_row_reductions h D structural hnone fixedFree reducible
    (fun C => C.omega_le_of_original_hypotheses h D structural hnone)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
