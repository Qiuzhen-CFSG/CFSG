module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Ordinary components containing perfect subgroups

A nonabelian subgroup determines an ordinary component containing it, since
distinct ordinary components commute. Its normalizer consequently preserves
that component. The orbit bound also makes perfect actors normalize every
ordinary component in a group of odd rank at most two.
Source: Aschbacher–Smith, C.3.2–3, printed p.149.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A nonabelian subgroup determines any ordinary component containing it. -/
theorem IsComponent.normalizer_le_of_nonabelian_subgroup
    {K L : Subgroup G} (hK : IsComponent G K) (hLK : L ≤ K)
    (hne : ⁅L,L⁆ ≠ ⊥) : normalizer (L : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hneq
  have hLL : L ≤ K.map (MulAut.conj g).toMonoidHom := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hLK
    rw [MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp hg] at hm
    exact hm
  exact hne (bot_unique ((commutator_mono hLL hLK).trans
    ((hK.map_conj g).commutator_eq_bot_of_ne hK hneq).le))

/-- Perfect actors fix every ordinary component when its orbit has size at most two. -/
theorem IsComponent.perfect_le_normalizer_of_odd_rank_le_two [Finite G]
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    {K : Subgroup G} (hK : IsComponent G K) (L : Subgroup G) [Group.IsPerfect L] :
    L ≤ normalizer (K : Set G) := by
  rcases hK.normal_or_index_two_of_odd_rank_le_two hrank with hn|hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · exact le_of_isPerfect_of_index_eq_two L _ hi
end Theory.GroupTheory
