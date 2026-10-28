module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The first normality deductions in 13.5.15

Work with the original F.9.1 setup: L₁ is O²(C_L(V₁)), and U_H is
the H-closure of V₃. The earlier identity V₃=[V,L₁] and coprime
commutator idempotence give [V₃,L₁]=V₃. Relative normality in H
propagates this to U_H and places U_H inside the actual O₂(L₁).
This supplies the full-commutator premise of 13.5.14 before making
its G.2.4 substitution.

The source construction of F.9.1 and V₃=[V,L₁] remains with the
earlier §13.5 geometry. This module does not assert all of 13.5.15.
Its exact core intersection will also identify the kernel of L₁→H*.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.14(1) and the first paragraph of 13.5.15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

/-- The source seed identity gives commutator generation without G.2.4. -/
theorem seed_commutator (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆) : ⁅D.Vplus, D.L₁⁆ = D.Vplus := by
  have hp : IsPPerfect 2 D.L₁ :=
    isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)
  have hVL : D.L₁ ≤ normalizer (D.V : Set G) := by
    have hnormal : D.LT ≤ normalizer (D.V : Set G) :=
      (normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal
    exact ((map_subtype_le _).trans inf_le_left).trans (le_sup_left.trans hnormal)
  let := h.elementary
  rw [hseed]
  exact commutator_isPPerfect_idempotent D.L₁ D.V hp
    (IsElementaryAbelian.isPGroup 2 D.V) hVL

/-- The original H-closure lies in O₂(L₁), with normality only inside H. -/
theorem closure_reduction (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    D.UH = ⁅D.UH, D.L₁⁆ ∧ D.UH ≤ D.L₁.pCoreIn 2 ∧ D.UH ≤ D.L := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  have hnorm : D.H ≤ normalizer (D.L₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLH).mp hn
  have hc : ⁅D.UH, D.L₁⁆ = D.UH :=
    commutator_conjugateSpanBy_eq_self D.Vplus D.H D.L₁ hLH hnorm
      (seed_commutator h hseed)
  have hUL : D.UH ≤ D.L₁ := hc.ge.trans
    (le_normalizer_iff_commutator_le_right.mp (h.UH_le_H.trans hnorm))
  have hcore : D.UH ≤ D.L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes h.g2_hypothesis.U_isPGroup hUL
      (hLH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  exact ⟨hc.symm, hcore, hUL.trans ((map_subtype_le _).trans inf_le_left)⟩

/-- The tilde hypothesis in 13.5.14 follows before constructing its A₅ block. -/
theorem tilde_closure_commutator (h : D.Hypothesis)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ := by
  have hU : D.UH ≤ D.g2.G₁ := h.UH_le_H.trans h.g2_hypothesis.H_le
  have hL : D.L₁ ≤ D.g2.G₁ :=
    (le_sup_left.trans h.local_le).trans h.g2_hypothesis.H_le
  have hc : ⁅D.UH.subgroupOf D.g2.G₁, D.L₁.subgroupOf D.g2.G₁⁆ =
      D.UH.subgroupOf D.g2.G₁ := by
    apply map_injective D.g2.G₁.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hU,
      map_subgroupOf_eq_of_le hL, ← (closure_reduction h hseed hn).1]
  change (D.UH.subgroupOf D.g2.G₁).map _ =
    ⁅(D.UH.subgroupOf D.g2.G₁).map _, (D.L₁.subgroupOf D.g2.G₁).map _⁆
  rw [← map_commutator, hc]

/-- The kernel intersection uses the intrinsic core of the original L₁. -/
theorem local_core_intersection (h : D.Hypothesis)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    D.L₁ ⊓ D.QH = D.L₁.pCoreIn 2 := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  apply le_antisymm (inf_pCoreIn_le_of_le 2 hLH)
  exact le_inf (pCoreIn_le 2 D.L₁)
    (pCoreIn_mono_of_normalizes hLH ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
