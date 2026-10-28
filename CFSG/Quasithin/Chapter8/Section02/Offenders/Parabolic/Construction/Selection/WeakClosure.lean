module

public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure

/-!
# Positive weak closure from the preceding parameter bounds

The first implication is the comparison in 7.3.3; the second is the
FWCI argument for the M₂₂ code case in 7.5.6(1). They concern the actual
subgroup V, automizer, and global weak-closure parameters. The source
owners `qt-7-01-05` and `qt-8-01` still supply the representation bounds
and remaining case eliminations from Hypotheses 7.0.2/7.3.1/8.2.1.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}

/-- The positive gap between m and a forces positive w, using 7.3.3. -/
theorem globalW_pos_of_local_parameter_gap (hT : HypothesisE322 V T)
    (hr : (localM V : ℕ∞) ≤ globalR V) (ha : localA V < (localM V : ℕ∞)) :
    0 < globalW V T := by
  have hb := Chapter7.localM_le_globalW_add_localA hT hr
  by_contra hn
  have he : globalW V T = 0 := le_antisymm (le_of_not_gt hn) bot_le
  rw [he, zero_add] at hb
  exact (not_lt_of_ge hb) ha

/-- The code-row argument in 7.5.6(1), using the actual FWCI. In that row
r ≥ 6 and m₂ ≤ 5 supply the strict gap. -/
theorem globalW_pos_of_fwci_gap (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : (primeRank 2 (Automizer V) : ℕ∞) < globalR V) : 0 < globalW V T := by
  have hb := lemma_E_3_29 hT (Or.inr hFF)
  by_contra hn
  have he : globalW V T = 0 := le_antisymm (le_of_not_gt hn) bot_le
  rw [he, add_zero] at hb
  exact (not_lt_of_ge hb) hr

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
