module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Reductions
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.CentralizerComponents
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.Linear
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.TableRows
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.Transport

/-!
# Displacement-fixer bounds for non-two-central M₁₂ involutions

A residual subgroup E isomorphic to A₅, centralized by an involution t and
normalized by its full centralizer, acts faithfully on [V,t]. Consequently
the kernel of C_G(t) on [V,t] centralizes E. The ambient embedding injects
this kernel into the full automorphism fixer of the corresponding native A₅;
its residual intersection injects into the native inner centralizer. The
proved intrinsic bounds give orders at most four and two, respectively.

For each involution that is not two-central in G, `CentralizerComponents`
constructs E from the genuine table rows in `TableRows`. Its Sylow argument
establishes ambient two-centrality of the excluded inner class. Combining
this construction with the action calculation proves both fixer bounds.
Only the inner centralizer row, outer fixed-subgroup row and outer involution
fusion remain explicit table premises, to be discharged by H.11 source assembly.

Source: Aschbacher–Smith H.11.1(5), printed pp.392–393, combined manuscript
of 1 March 2004. The final quadratic alternative is assembled by `LocalActors`.
-/

public section

open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

include d in
/-- The displacement-fixer calculation, with the actual normalized residual A₅ explicit. -/
theorem bounds_of_normal_a5 [FiniteDimensional (ZMod 2) V]
    (hfusion : OuterInvolutionFusion) {t : G} (ht : orderOf t = 2)
    (E : Subgroup G) (e : E ≃* alternatingGroup (Fin 5))
    (hEL : E ≤ solvableResidual G) (hEC : E ≤ centralizer ({t} : Set G))
    (hEN : centralizer ({t} : Set G) ≤ normalizer (E : Set G)) :
    Nat.card (involutionDisplacementFixer ρ t) ≤ 4 ∧
      Nat.card (involutionDisplacementFixer ρ t ⊓ solvableResidual G : Subgroup G) ≤ 2 := by
  have hr : 4 ≤ fixedCodim ρ (zpowers t) := by
    by_cases htL : t ∈ solvableResidual G
    · rw [fixedCodim_residual_involution ρ h htL ht]
    · rw [fixedCodim_outer_involution ρ h d hfusion htL ht]
      decide
  apply centralizing_a5_bounds ρ h d E _ e hEL
  exact fixer_centralizes_of_faithful ρ t E hEC hEN (fun x hx hf =>
    a5_faithful_on_displacement ρ h.faithful (h.finrank_eq_ten ρ) ht hr E e hEC hx hf)

include d in
/-- Both displacement-fixer bounds for a non-two-central involution, conditional
only on the genuine involution-table premises. -/
theorem bounds_of_not_twoCentral [FiniteDimensional (ZMod 2) V]
    (hfusion : OuterInvolutionFusion) (hin : InnerCentralizerRow)
    (hout : OuterFixedSubgroupRows) (t : G) (ht : orderOf t = 2)
    (hnt : ¬ TwoCentral t) :
    Nat.card (involutionDisplacementFixer ρ t) ≤ 4 ∧
      Nat.card (involutionDisplacementFixer ρ t ⊓ solvableResidual G : Subgroup G) ≤ 2 := by
  obtain ⟨E, e, hEL, hEC, hEN⟩ := exists_normal_residual_a5 ρ h d hin hout t ht hnt
  exact bounds_of_normal_a5 ρ h d hfusion ht E e hEL hEC hEN

include d in
/-- The kernel of C_G(t) on [V,t] has order at most four. -/
theorem card_le_four [FiniteDimensional (ZMod 2) V]
    (hfusion : OuterInvolutionFusion) (hin : InnerCentralizerRow)
    (hout : OuterFixedSubgroupRows) (t : G) (ht : orderOf t = 2)
    (hnt : ¬ TwoCentral t) : Nat.card (involutionDisplacementFixer ρ t) ≤ 4 :=
  (bounds_of_not_twoCentral ρ h d hfusion hin hout t ht hnt).1

include d in
/-- The residual part of the kernel of C_G(t) on [V,t] has order at most two. -/
theorem residual_card_le_two [FiniteDimensional (ZMod 2) V]
    (hfusion : OuterInvolutionFusion) (hin : InnerCentralizerRow)
    (hout : OuterFixedSubgroupRows) (t : G) (ht : orderOf t = 2)
    (hnt : ¬ TwoCentral t) :
    Nat.card (involutionDisplacementFixer ρ t ⊓ solvableResidual G : Subgroup G) ≤ 2 :=
  (bounds_of_not_twoCentral ρ h d hfusion hin hout t ht hnt).2

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
