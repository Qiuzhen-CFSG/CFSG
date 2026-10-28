module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalHypotheses

/-!
# Normality of the residual centralizer in the original Sylow subgroup

In the original C.5 configuration with R = T_H, put D = R ∩ C_G(K).
The residual K centralizes D. The Sylow subgroup R normalizes both R and
C_G(K), since K is normal in H. As H = KR, the whole group H normalizes D.
This supplies the actual normal subgroup used in original14.6.9; no
conclusion about the larger normalizer's characteristic is assumed.

Source: Aschbacher--Smith C.5.1 and14.6.9, printed pp.154 and1026.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

/-- The actual residual centralizer is normalized by the whole C.5 group. -/
theorem OriginalHypotheses.sylow_centralizer_normalized
    {H M K R : Subgroup G} (c : OriginalHypotheses H M K R R) :
    H ≤ normalizer (R ⊓ centralizer (K : Set G) : Set G) := by
  have hK : K ≤ centralizer (R ⊓ centralizer (K : Set G) : Set G) :=
    le_centralizer_iff.mp inf_le_right
  have hR : R ≤ normalizer (R ⊓ centralizer (K : Set G) : Set G) :=
    (le_inf R.le_normalizer
      (c.T_le_H.trans (c.normalizes_residual.trans
        (normalizer_le_normalizer_centralizer K)))).trans
      inf_normalizer_le_normalizer_inf
  rw [←c.residual_sup_sylow]
  exact sup_le (hK.trans (centralizer_le_normalizer _)) hR

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
