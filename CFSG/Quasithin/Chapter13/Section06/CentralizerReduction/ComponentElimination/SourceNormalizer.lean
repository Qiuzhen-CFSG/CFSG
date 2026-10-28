module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation

/-!
# Normalizer transport for 13.6.21

Normalization survives restriction to C_G(v) and its literal star map.
Since Lᵥ is normal in Mᵥ, a component contained in M would therefore
normalize Lᵥ*. This contradicts the star-action obstruction obtained
from the component analysis after 13.6.20. That obstruction remains a
separate input; no component classification is asserted here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 13.6.21, printed p.932.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
open ComponentSelection
variable {G : Type*} [Group G]

/-- Restriction and the actual star map carry normalizing actors to
normalizing actors. -/
theorem starImage_normalizes_of_normalizes (A B : Subgroup G) (z v : G)
    (hB : B ≤ Gv v) (hAB : A ≤ normalizer (B : Set G)) :
    starImage z v A ≤ normalizer (starImage z v B : Set (Gstar z v)) := by
  have hn : A.subgroupOf (Gv v) ≤ normalizer (B.subgroupOf (Gv v) : Set (Gv v)) := by
    rw [← subgroupOf_normalizer_eq hB]
    exact comap_mono hAB
  exact (map_mono hn).trans (le_normalizer_map _)

/-- The local group implication in 13.6.21 uses relative normality in Mᵥ
and the actual star-action obstruction. Its model proof remains separate. -/
theorem not_le_M_of_star_action_obstruction (L M K : Subgroup G) (z v : G)
    (hL : Lv L v ≤ Mv M v) (hN : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (hK : K ≤ Gv v)
    (hstar : ¬ starImage z v K ≤ normalizer (starImage z v (Lv L v) : Set (Gstar z v))) :
    ¬ K ≤ M := by
  intro hKM
  have hKMv : K ≤ Mv M v := le_inf hKM hK
  have hn : K ≤ normalizer (Lv L v : Set G) :=
    hKMv.trans ((normal_subgroupOf_iff_le_normalizer hL).mp hN)
  exact hstar (starImage_normalizes_of_normalizes K (Lv L v) z v (Lv_le_Gv L v) hn)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source
