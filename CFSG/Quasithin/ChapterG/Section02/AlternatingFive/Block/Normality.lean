module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.TerminalReduction
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Chapter13
public import Theory.GroupTheory.PCoreImage

/-!
# Relative normality supplies the terminal hypotheses

If the actual point-stabilizer residual L₁ is normal in H, the identity
[V,L₁]=V propagates to U=⟨Vᴴ⟩. Mapping to N_G(V₁)/V₁ gives the first
hypothesis of G.2.4(8). Relative monotonicity of the two-core gives the
second. No ambient normality or block conclusion is assumed.

The §13.5 application retains the identity of its original L₁ with the
residual constructed from L⁻. These are the premise-discharge steps in
13.5.15, not the subsequent block and quaternion recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335; 13.5.14–15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

namespace Hypothesis

/-- Normality is relative to H. The conclusion is the literal ambient
commutator, before applying either quotient map. -/
theorem U_commutator_of_local_normal (d : Hypothesis D g)
    (hn : (D.L₁.subgroupOf D.H).Normal) : ⁅D.U, D.L₁⁆ = D.U := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans d.setup.local_le
  exact commutator_conjugateSpanBy_eq_self D.V D.H D.L₁ hLH
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hn) d.seed_eq_commutator

/-- Both extra hypotheses of G.2.4(8) follow from L₁ normal in H. -/
theorem terminal_premises_of_local_normal (d : Hypothesis D g)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U ∧ D.L₁.pCoreIn 2 ≤ D.QH := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans d.setup.local_le
  have hUG : D.U ≤ D.G₁ := d.setup.U_le_H.trans d.setup.H_le
  have hLG : D.L₁ ≤ D.G₁ := hLH.trans d.setup.H_le
  have hc : ⁅D.U.subgroupOf D.G₁, D.L₁.subgroupOf D.G₁⁆ =
      D.U.subgroupOf D.G₁ := by
    apply map_injective D.G₁.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUG,
      map_subgroupOf_eq_of_le hLG, d.U_commutator_of_local_normal hn]
  refine ⟨?_, pCoreIn_mono_of_normalizes hLH
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hn)⟩
  change ⁅(D.U.subgroupOf D.G₁).map _, (D.L₁.subgroupOf D.G₁).map _⁆ = _
  rw [← map_commutator, hc]
  rfl

/-- Applying the terminal lifting gives the actual two-core containment
and I=L from relative normality and the earlier generation clause. -/
theorem terminal_reduction_of_local_normal (d : Hypothesis D g)
    (hn : (D.L₁.subgroupOf D.H).Normal) (hgen : D.I g = D.L ⊔ D.U) :
    D.U = ⁅D.U, D.L₁⁆ ∧ D.U ≤ D.L₁.pCoreIn 2 ∧
      D.L₁.pCoreIn 2 ≤ D.QH ∧ D.I g = D.L := by
  obtain ⟨hfull, hcore⟩ := d.terminal_premises_of_local_normal hn
  obtain ⟨he, hle⟩ := d.terminal_reduction hfull
  exact ⟨he, hle, hcore, d.terminal_group_eq hfull hgen⟩

end Hypothesis

/-- The literal premise discharge for 13.5.15. In particular the original
L₁ is not silently replaced by the newly constructed residual. -/
theorem chapter13_terminal_premises
    (V₁ V₃ Lminus T H L₁ : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal) :
    let D := chapter13Setup V₁ V₃ Lminus T H
    ⁅D.tilde (conjugateSpanBy V₃ H), D.tilde L₁⁆ =
      D.tilde (conjugateSpanBy V₃ H) ∧ L₁.pCoreIn 2 ≤ H.pCoreIn 2 := by
  subst L₁
  exact d.terminal_premises_of_local_normal hn

/-- The generated group K in 13.5.14–15 equals L⁻; its original H-closure
lies in O₂(L₁). The remaining conclusions require the terminal collapse. -/
theorem chapter13_terminal_reduction
    (V₁ V₃ Lminus T H L₁ K : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hn : (L₁.subgroupOf H).Normal)
    (hK : K = conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g)
    (hgen : K = Lminus ⊔ conjugateSpanBy V₃ H) :
    conjugateSpanBy V₃ H = ⁅conjugateSpanBy V₃ H, L₁⁆ ∧
      conjugateSpanBy V₃ H ≤ L₁.pCoreIn 2 ∧
      L₁.pCoreIn 2 ≤ H.pCoreIn 2 ∧ K = Lminus := by
  subst L₁
  subst K
  exact d.terminal_reduction_of_local_normal hn hgen

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
