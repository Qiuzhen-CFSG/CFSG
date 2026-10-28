module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.NormalizerFixedLine
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer

/-!
# A cubic fixes the prescribed Sylow-fixed A5 vector

The Sylow normalizer contains an element of order three. It preserves the
layer's Sylow-fixed subgroup, whose order is at most two, and therefore
fixes the original vector. The ambient form retains the original block,
Sylow intersection and element.

Source: Aschbacher–Smith 10.2.1, printed p.743, using C.1.13(c).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open ChapterC

theorem alternatingFive_exists_cubic_fixing_sylow_vector
    {K : Type*} [Group K] [Finite K] (hK : IsAlternatingBlock K 5)
    (P : Sylow 2 K) (v : K) (hv : v∈blockU K)
    (hvP : v∈centralizer (P:Set K)) :
    ∃ x : K, orderOf x=3 ∧ x∈centralizer ({v}:Set K) := by
  let F := blockU K ⊓ centralizer (P:Set K)
  have hNF : normalizer (P:Set K)≤normalizer (F:Set K) := by
    apply le_trans (le_inf ?_ (normalizer_le_normalizer_centralizer (P:Subgroup K)))
      inf_normalizer_le_normalizer_inf
    rw [(blockU K).normalizer_eq_top]
    exact le_top
  have hNC : normalizer (P:Set K)≤centralizer (F:Set K) := by
    by_cases he : F=⊥
    · intro x hx z hz
      have hz1 : z=1 := mem_bot.mp (he ▸ hz)
      simp [hz1]
    · have hcard : Nat.card F=2 := by
        have hlo := F.one_lt_card_iff_ne_bot.mpr he
        have hhi := hK.sylow_fixed_card_le_two P
        change Nat.card F≤2 at hhi
        omega
      exact hNF.trans (normalizer_le_centralizer_of_card_two F hcard)
  obtain ⟨x,hx,hx3⟩ := hK.exists_sylow_normalizer_cubic P
  refine ⟨x,hx3,?_⟩
  exact (centralizer_le (show ({v}:Set K)⊆F from Set.singleton_subset_iff.mpr ⟨hv,hvP⟩)) (hNC hx)

theorem alternatingFive_exists_ambient_cubic_fixing_sylow_vector
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hR : Chapter1.IsSylowIn 2 R K)
    (v : G) (hv : v∈(blockU K).map K.subtype) (hvR : v∈centralizer (R:Set G)) :
    ∃ x : G, x∈K ∧ orderOf x=3 ∧ x∈centralizer ({v}:Set G) := by
  obtain ⟨P,hP⟩ := hR
  obtain ⟨w,hw,rfl⟩ := hv
  have hwP : w∈centralizer (P:Set K) := by
    intro p hp
    exact Subtype.ext (hvR p (hP ▸ mem_map_of_mem K.subtype hp))
  obtain ⟨x,hx3,hxw⟩ := alternatingFive_exists_cubic_fixing_sylow_vector hK P w hw hwP
  refine ⟨x,x.property,(orderOf_coe x).trans hx3,?_⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg K.subtype (mem_centralizer_singleton_iff.mp hxw))

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
