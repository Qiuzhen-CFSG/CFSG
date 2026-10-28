module
public import Theory.GroupTheory.CentralProductCubicFamily
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
/-! A cubic centralizing a perfect subgroup selects a unique component
support. The source orbit bound makes that cubic normalize every component,
and the finite central-product cut then gives containment. This is the
component projection step in source2.4.25, printed p542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03
variable {G : Type*} [Group G] [Finite G]

theorem perfect_subgroup_le_cComponent_of_cubic_centralizer
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (L : Subgroup G) [Group.IsPerfect L] (hL0 : L ≠ ⊥)
    (hL : L ≤ cComponentLayer G)
    (hcyc : ∀ P : Sylow 3 L, IsCyclic P) (hres : primeToResidual 3 L = ⊤)
    (b : G) (hb : orderOf b = 3) (hbL : b ∈ centralizer (L : Set G)) :
    ∃ K : Subgroup G, K.IsCComponent ∧ L ≤ K := by
  have hnorm (K : Subgroup G) (hK : K.IsCComponent) : b ∈ normalizer (K : Set G) := by
    rcases ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (CComponentCommutation.noncentralStructureInput κ) hG hO hK with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact mem_top b
    · exact (zpowers_le.mpr ((normalizer (K : Set G)).sq_mem_of_index_two hi b))
        (mem_zpowers_pow_iff.mpr (by rw [hb]; decide))
  exact perfect_subgroup_le_member_of_cubic_centralizer {K | K.IsCComponent}
    (fun K hK C hC hne => commutator_eq_bot_iff_le_centralizer.mp
      (CComponentCommutation.commutator_eq_bot hG hO hK hC hne))
    L hL0 hL hcyc hres b hb hnorm hbL (hG.stronglyQuasithin 3 (by decide) (by decide))
end CFSG.Quasithin.ChapterA.Section03
