module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Reductions
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!+# The group-table premises permitted in the H.11 displacement calculation

These statements concern the actual native M₁₂ centralizer and the fixed
subgroups of actual outer automorphisms. They contain no module-action
conclusions. The inner row uses the ATLAS fixed-point-free 2A representative;
the outer row ranges over every involutory outer automorphism. Their producers
are the existing M₁₂ involution-table tasks. H.11 source assembly must discharge
both rows, as well as outer involution fusion.

Source: Aschbacher–Smith H.11.1, printed pp.392–393, citing GLS3 Table 5.3b.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
open Subgroup Sporadic.Mathieu

/-- The genuine centralizer row for the noncentral inner involution class. -/
def InnerCentralizerRow : Prop :=
  Nonempty ((centralizer ({m12Involution2A} : Set M12)) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))

/-- The genuine fixed-subgroup row for all involutory outer automorphisms. -/
def OuterFixedSubgroupRows : Prop :=
  ∀ a : MulAut M12, orderOf a = 2 → a ∉ MulAut.innerSubgroup M12 →
    Nonempty (a.fixedSubgroup ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 5))

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
