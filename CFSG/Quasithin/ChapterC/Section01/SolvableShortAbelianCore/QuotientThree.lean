module

public import CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore
import all CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore

/-!
# Short groups with quotient of order three

The existing proof of C.1.8 first shows O₂(B) = U(B) whenever B/O₂(B)
has order three. Thus the elementary clause of shortness already makes the
core abelian, and the invariant-four-group argument gives |B| = 12.
No additional solvability or abelian-core premise is needed.

This is an internal proof extension: `import all` reuses the two private
steps of `SolvableShortAbelianCore` without changing that module's public
boundary or rebuilding its consumers. The exported statement mentions only
the original short-group definition.

Source: Aschbacher–Smith C.1.7–13, printed pp.123–125. The M₂₄ sextet
block obstruction uses this consequence for the cubic quotient branch.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory

/-- A short group with cubic two-core quotient has order twelve. -/
theorem IsShort.card_eq_twelve_of_quotient_three {B : Type*} [Group B]
    (h : IsShort B) (hq : Nat.card (B ⧸ pCore 2 B) = 3) : Nat.card B = 12 := by
  let := h.finite
  have hU : pCore 2 B = blockU B := core_eq_U h hq
  let : IsElementaryAbelian 2 (pCore 2 B) := hU ▸ h.elementary
  have hP := core_four h hq
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hq, hP] at he
  exact he

end CFSG.Quasithin.ChapterC
end
