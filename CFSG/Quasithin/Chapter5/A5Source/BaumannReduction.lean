module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer

/-!
# The original A5 Baumann normalizer reduction

The actual source context gives the local core as C_T(V), with unique
maximal two-local overgroup N(L). If J(T) centralizes V, heredity makes
Baum(T) the Baumann subgroup of that core, hence LT-normal; uniqueness
controls its full normalizer. Otherwise an escaping Baumann normalizer
excludes every nontrivial characteristic subgroup normal in LT and gives
exactly the normalizer obstruction needed by C.6.3 on the original groups.

Source: Aschbacher--Smith 5.1.2 and 5.1.7(1), printed pp.630,633--634.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- Unique local control on the literal source LT-normal two-subgroups. -/
theorem normalizer_of_local_normal (W : Subgroup G) (hne : W ≠ ⊥)
    (hWT : W ≤ (T : Subgroup G))
    (hn : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
    normalizer (W : Set G) ≤ normalizer (L : Set G) :=
  normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le hWT) hne
    ((normal_subgroupOf_iff_le_normalizer (hWT.trans le_sup_right)).mp hn)

/-- The centralizing branch of the original 5.1.7(1). -/
theorem baumann_normalizer_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let := d.elementary
  have hB : baumann (T : Subgroup G) = baumann ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
    rw [lemma_B_2_3_5 (T : Subgroup G) V d.chosen.le_sylow hJ,
      d.sylow_centralizer d.normalizes_L]
  have hN : L ⊔ (T : Subgroup G) ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
    rw [hB]
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans
        (normalizer_le_normalizer_baumann _)
  have hVB : V ≤ baumann (T : Subgroup G) := by
    apply le_inf d.chosen.le_sylow
    exact (le_centralizer_iff.mp hJ).trans
      (centralizer_le (map_subtype_le _))
  exact normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le inf_le_left)
    (fun hb => d.chosen.ne_bot (bot_unique (hVB.trans_eq hb))) hN

/-- The C.6.2 normalizer obstruction follows from the original escape. -/
theorem baumann_normalizer_obstruction
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hne : W ≠ ⊥) (hWB : W ≤ baumann (T : Subgroup G))
    (hn : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
    ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (W : Set G) :=
  fun h => hout (h.trans (normalizer_of_local_normal d W hne (hWB.trans inf_le_left) hn))

/-- This is the precise characteristic-subgroup premise of E.2.3(4). -/
theorem no_characteristic_baumann_of_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (D : Subgroup (baumann (T : Subgroup G))) (hD : D.Characteristic)
    (hn : ((D.map (baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal) : D = ⊥ := by
  let := hD
  by_contra hne
  exact baumann_normalizer_obstruction d hout _
    (fun h => hne ((D.map_eq_bot_iff_of_injective (baumann (T : Subgroup G)).subtype_injective).mp h))
    (map_subtype_le _) hn (normalizer_le_normalizer_characteristic_image _ D)

end CFSG.Quasithin.Chapter5.A5Source
