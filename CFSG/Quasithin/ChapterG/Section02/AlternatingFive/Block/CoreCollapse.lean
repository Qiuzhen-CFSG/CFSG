module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.CoreCollapse.ChiefFactors
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.CoreCollapse.Natural

/-!
# The terminal core collapse in G.2.4(8)

Under exactly the two extra hypotheses of clause (8), the actual local
plus image is cyclic of order three and there are no further central
L₁-sections on U above V₁. This collapses S₂ to V_L. A cubic starred
L₁-element acts freely on the genuine natural upper quotient, including
when there are zero summands, giving S=[S,L₁]V_L. The existing centrality
argument then yields S=V_L.

The records EarlierStructure and EarlierUpper contain only earlier
clauses (1–7). Their producers are discharged by the enclosing G.2.4
assembly. No core equality, cubic-image premise, or block recognition
is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  {F : Type*} [Field F] {s : ℕ}
  [((S₂ D g).subgroupOf (D.S g)).Normal]

/-- The natural-module step in the original ambient group. -/
theorem terminal_core_eq_commutator_sup_first (d : Hypothesis D g)
    (c : EarlierStructure D g) (e : EarlierUpper D g c F s)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) : D.S g = ⁅D.S g, D.L₁⁆ ⊔ D.VL := by
  obtain ⟨t, htL, ht⟩ := d.terminal_exists_local_cubic_star c
  have hcomm := e.natural.core_eq_commutator_sup_second t htL ht
    (d.second_le_core c.L_le_I)
  rwa [d.terminal_second_eq_first c hfull hcore] at hcomm

/-- Both missing terminal bounds, with no further chief-factor or action premises. -/
theorem terminal_core_bounds (d : Hypothesis D g)
    (c : EarlierStructure D g) (e : EarlierUpper D g c F s)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) :
    S₂ D g = D.VL ∧ D.S g ≤ D.L₁.pCoreIn 2 ⊔ D.VL :=
  ⟨d.terminal_second_eq_first c hfull hcore,
    d.core_le_local_core_sup_first_of_commutator c hfull
      (d.terminal_core_eq_commutator_sup_first c e hfull hcore)⟩

/-- The core-collapse conclusion of G.2.4(8), using its literal upper action. -/
theorem terminal_core_eq_first (d : Hypothesis D g)
    (c : EarlierStructure D g) (e : EarlierUpper D g c F s)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) : D.S g = D.VL := by
  obtain ⟨hsecond, hbound⟩ := d.terminal_core_bounds c e hfull hcore
  exact d.core_eq_first_of_terminal_bounds c e hcore hsecond hbound

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
