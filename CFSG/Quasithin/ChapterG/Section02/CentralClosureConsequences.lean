module
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.CentralizerModulo

/-!
# The original closure inside the local two-core

G.2.2 makes U a normal two-subgroup of H and central modulo the point.
We expose the corresponding ambient inclusions U≤O₂(H) and
[U,O₂(H)]≤V₁, preserving the literal tilde quotient. They are the inputs
used by the opposite-core intersection calculation in G.2.3.

Source: Aschbacher–Smith G.2.2(1), printed p.332.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

theorem Hypothesis.U_le_core (h : D.Hypothesis) : D.U ≤ D.QH :=
  le_pCoreIn_of_normalizes h.U_isPGroup h.U_le_H
    (le_normalizer_conjugateSpanBy D.V D.H)

theorem Hypothesis.commutator_U_core_le_point (h : D.Hypothesis) :
    ⁅D.U, D.QH⁆ ≤ D.V₁ := by
  apply commutator_le.mpr
  intro u hu q hq
  let f := QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
  let ui : D.G₁ := ⟨u, h.H_le (h.U_le_H hu)⟩
  let qi : D.G₁ := ⟨q, h.H_le (pCoreIn_le 2 D.H hq)⟩
  have hu' : f ui ∈ (center (D.tilde D.QH)).map (D.tilde D.QH).subtype :=
    omegaOneAmbient_le _ (h.tilde_U_central.2 ⟨ui, hu, rfl⟩)
  have hq' : f qi ∈ D.tilde D.QH := ⟨qi, hq, rfl⟩
  obtain ⟨v, hv, he⟩ := hu'
  have hvq := (mem_center_iff.mp hv) ⟨f qi, hq'⟩
  have hc : f ui * f qi = f qi * f ui := by
    have hh : (v : D.Tilde) * f qi = f qi * (v : D.Tilde) :=
      (congrArg Subtype.val hvq).symm
    change (v : D.Tilde) = f ui at he
    rwa [he] at hh
  have hone : f ⁅ui, qi⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc
  exact (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁) ⁅ui, qi⁆).mp hone

end CFSG.Quasithin.ChapterG.Section02.Setup
