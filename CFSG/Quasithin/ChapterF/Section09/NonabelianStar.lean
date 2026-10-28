module
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Maps

/-!
# Nontriviality of the closure image in the original F.9 setup

If the image of U_H in LT/O₂(LT) were trivial, U_H would lie in the
Sylow centralizer of V. Then V₊ would centralize its entire H-closure,
forcing that closure to be abelian. This supplies the nontrivial starred
closure required by13.5.14 in both natural alternating degrees.
Source: Aschbacher–Smith13.5.14(2), printed p.919.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- Nonabelian U_H has nontrivial image under the original LT-core quotient. -/
theorem nonabelian_star_ne_bot (h : D.Hypothesis) (hU : ¬ IsMulCommutative D.UH) :
    D.g2.star D.UH ≠ ⊥ := by
  have huLT : D.UH ≤ D.LT := h.UH_le_QH.trans (h.QH_le_T.trans le_sup_right)
  intro he
  have hcore : D.UH ≤ D.LT.pCoreIn 2 := by
    intro x hx
    let y : D.LT := ⟨x,huLT hx⟩
    have hy : QuotientGroup.mk' (pCore 2 D.LT) y = 1 := by
      have hm : QuotientGroup.mk' (pCore 2 D.LT) y ∈ D.g2.star D.UH :=
        mem_map_of_mem _ hx
      rw [he] at hm
      exact hm
    exact mem_map_of_mem D.LT.subtype ((QuotientGroup.eq_one_iff y).mp hy)
  have hc : D.UH ≤ centralizer (D.V : Set G) :=
    hcore.trans (h.sylow_centralizer.symm.le.trans inf_le_right)
  exact hU ((conjugateSpanBy_commutative_iff D.Vplus D.H).mpr
    (h.plus_le.trans (le_centralizer_iff.mp hc)))

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
