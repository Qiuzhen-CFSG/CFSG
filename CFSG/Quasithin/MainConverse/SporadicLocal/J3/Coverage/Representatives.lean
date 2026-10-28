module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Generators
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic.FinCases

/-!
# Fixed representatives for the J₃ elementary-normalizer calculation

The five subgroups below use only the already published word-defined
generators. They are aligned with the three fixed local candidates: the
intended normalizer containments have indices 0, 1, 2, 1, 1. In particular,
the involution representative is the standard involution itself.

This module fixes the shared objects for two independent calculations:
exhaustion up to ambient conjugacy of the elementary subgroups in the Sylow
candidate, and the ambient normalizers of these five subgroups. Neither
calculation is asserted by the definitions. Only the elementary order-two
case and the containments in the elementary candidate are proved here.

Source: GLS, Number 3, Table 5.3h, printed p.269. The table lists the three
maximal two-locals, rather than these five elementary representatives.
The latter are a computational route to the table's coverage assertion.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

/-- The first published elementary generator is the standard involution. -/
public theorem elementaryGenerator_zero : elementaryGenerator 0 = a := by
  apply Subtype.ext
  simp [elementaryGenerator, chainElement, elementaryWord0, elementaryWord1,
    elementaryWord2, Theory.GroupTheory.evalWord, OrderCertificate.L0Gen, a]

/-- The first published Sylow generator is the same standard involution. -/
public theorem sylowGenerator_zero : sylowGenerator 0 = a := by
  apply Subtype.ext
  simp [sylowGenerator, chainElement, sylowWord0, sylowWord1,
    sylowWord2, Theory.GroupTheory.evalWord, OrderCertificate.L0Gen, a]

/-- Five actual subgroups, whose exhaustive conjugacy property is a separate
obligation. The two order-four candidates use different pairs of generators. -/
@[expose] public def elementaryRepresentative : Fin 5 → Subgroup Model
  | 0 => zpowers a
  | 1 => zpowers (elementaryGenerator 0) ⊔ zpowers (elementaryGenerator 1)
  | 2 => zpowers (elementaryGenerator 0) ⊔ zpowers (elementaryGenerator 2)
  | 3 => (zpowers (elementaryGenerator 1) ⊔ zpowers (elementaryGenerator 2)) ⊔
      zpowers (elementaryGenerator 3)
  | 4 => elementaryCandidate

/-- The local candidate in which each representative's normalizer must lie.
This definition does not assert the containment. -/
@[expose] public def representativeLocal : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1

/-- All five chosen representatives lie in the fixed elementary candidate. -/
public theorem elementaryRepresentative_le_elementaryCandidate (i : Fin 5) :
    elementaryRepresentative i ≤ elementaryCandidate := by
  have hgen (j : Fin 4) : zpowers (elementaryGenerator j) ≤ elementaryCandidate :=
    zpowers_le.mpr (elementaryGenerator_mem j)
  have ha : zpowers a ≤ elementaryCandidate := by
    simpa only [elementaryGenerator_zero] using hgen 0
  fin_cases i
  · exact ha
  · exact sup_le (hgen 0) (hgen 1)
  · exact sup_le (hgen 0) (hgen 2)
  · exact sup_le (sup_le (hgen 1) (hgen 2)) (hgen 3)
  · exact le_rfl

/-- The involution representative belongs to the fixed Sylow candidate. -/
public theorem elementaryRepresentative_zero_le_sylowCandidate :
    elementaryRepresentative 0 ≤ sylowCandidate := by
  apply zpowers_le.mpr
  simpa only [sylowGenerator_zero] using sylowGenerator_mem 0

public theorem elementaryRepresentative_zero_ne_bot : elementaryRepresentative 0 ≠ ⊥ :=
  fun h => a_ne_one (zpowers_eq_bot.mp h)

public theorem elementaryRepresentative_zero_elementary :
    IsElementaryAbelian 2 (elementaryRepresentative 0) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one a_sq

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
