module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.BlockSource
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# Component membership in the nonsolvable block conclusion

A short group's two-core quotient is quasisimple or has order three.
The second alternative makes the short group solvable; a solvable subnormal
generator together with a Sylow two-subgroup would make the whole group
solvable. Thus the selected block in the nonsolvable source is an actual
C-component, not merely a typed short subgroup.

Source: Aschbacher–Smith C.1.7, E.2.3(4), pp.123,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem nonsolvable_generating_block_isCComponent
    (hs : ¬Group.IsSolvable G) (L : Subgroup G) (hL : IsBlock L)
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤) : L.IsCComponent := by
  rcases hL.short.quotient with hq | h3
  · let := hq
    exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hL.subnormal hL.short.twoPerfect
  · let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card h3
    let : CommGroup (L ⧸ pCore 2 L) := IsMulCommutative.instCommGroup
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable L := (Group.isSolvable_iff_subgroup_quotient (pCore 2 L)).mpr
      ⟨inferInstance,inferInstance⟩
    exact (hs (LinearBlockSource.solvable_of_subnormal_solvable_sylow_generation L hL.subnormal T hgen)).elim

theorem source_nonsolvable_component_block
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G) (hs : ¬Group.IsSolvable G)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsBlock L ∧
      ((∃ n, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  obtain ⟨L,hL,ht,hm,hgen,hout⟩ := source_nonsolvable_block hG T hP hf hs U hU hJ hno
  exact ⟨L,nonsolvable_generating_block_isCComponent hs L hL T hgen,hL,ht,hm,hgen,hout⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
