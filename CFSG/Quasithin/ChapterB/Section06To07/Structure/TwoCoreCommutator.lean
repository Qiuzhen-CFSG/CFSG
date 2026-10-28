module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Centralization modulo a normal subgroup of a minimal parabolic

Let V lie in the chosen Sylow two-subgroup and move outside O₂(H).
If V centralizes O₂(H) modulo a normal subgroup W, the preimage of the
quotient centralizer is normal in H. It cannot lie in the core J of the
unique maximal overgroup: T ∩ J = O₂(H). The normal-subgroup dichotomy
therefore puts O²(H) in this centralizer.

This gives [O₂(H), O²(H)] ≤ W. The cyclic construction applies it to the
canonical orbit of O₂(H) ∩ V, before selecting an invariant odd Sylow.
Source: Aschbacher–Smith, B.6.8(4–5), printed pp.113–115; application to
the residual calculation in 12.2.22, printed p.803.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- A moving subgroup of the Sylow centralizing the two-core modulo W forces
its entire two-residual to centralize that same quotient. -/
theorem minimalParabolic_twoCore_commutator_le
    (T : Sylow 2 H) (hmin : IsMinimalParabolicOver T ⊤)
    (V W : Subgroup H) [W.Normal] (hVT : V ≤ T) (hVQ : ¬ V ≤ pCore 2 H)
    (hcomm : ⁅pCore 2 H, V⁆ ≤ W) : ⁅pCore 2 H, pResidual 2 H⁆ ≤ W := by
  let q := QuotientGroup.mk' W
  let Q := (pCore 2 H).map q
  let : Q.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective W)
  let C := (centralizer (Q : Set (H ⧸ W))).comap q
  let : C.Normal := inferInstance
  have hVC : V ≤ C := by
    have he : ⁅Q, V.map q⁆ = ⊥ := by
      rw [← map_commutator]
      exact (map_eq_bot_iff _ (f := q)).mpr (by
        simpa only [q, QuotientGroup.ker_mk'] using hcomm)
    have hcen := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    exact map_le_iff_le_comap.mp hcen
  have hKC : pResidual 2 H ≤ C := by
    rcases minimalParabolic_normal_subgroup_residual_dichotomy T hmin C with hCJ | hKC
    · exact (hVQ ((le_inf hVT (hVC.trans hCJ)).trans_eq
        (minimalParabolic_sylow_inf_core T hmin))).elim
    · exact hKC
  have he : ⁅Q, (pResidual 2 H).map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mpr (map_le_iff_le_comap.mpr hKC))
  rw [← map_commutator] at he
  have hk := (map_eq_bot_iff _ (f := q)).mp he
  simpa only [q, QuotientGroup.ker_mk'] using hk

end CFSG.Quasithin.ChapterB
