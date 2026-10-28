module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearBlockSource.Control
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearBlockSource.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
/-!
# A generating χ₀ block from the original Baumann Sylow branch

Apply the proved C.1.29 inside `O²(G) Baum(T)` to its proper characteristic
control subgroup. A factor outside the original unique maximal overgroup
lifts to an actual χ₀ block and generates `G` together with `T`.
The Thompson subgroup is preserved because `J(Baum(T)) = J(T)`.

Source: Aschbacher--Smith E.2.3(4), pp.216--217. The conclusion retains the
alternating-three possibility in the solvable case under the block definitions
of C.1.12; the nonsolvable specialization is in `Nonsolvable`.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
open ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]

theorem chiZero_block_of_baumann_sylow
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G)
    (hno : ∀ C : Subgroup (baumann (T : Subgroup G)), C.Characteristic →
      (C.map (baumann (T : Subgroup G)).subtype).Normal → C = ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (residualBaumannJoin T)) :
    ∃ L : Subgroup G, IsChiZeroBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  let N := residualBaumannJoin T
  let M := minimalParabolicMax T hP
  obtain ⟨S,hS⟩ := hSyl
  obtain ⟨hcontrol,hproper⟩ := residualBaumannJoin_control T hP (fun C hC hne hn => hne (hno C hC hn)) S hS
  obtain ⟨r,hr,K,hK,hout,hm,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple (hG.subgroup N)
      (residualBaumannJoin_fitting T hf) S (M.subgroupOf N) hcontrol
  have hrpos : 0 < r := by
    by_contra! hh
    have hz : r = 0 := Nat.eq_zero_of_le_zero hh
    subst r
    apply hproper
    apply top_unique
    intro g _
    obtain ⟨m,b,hg⟩ := hprod g
    have hg' : g = (m : N) := by simpa only [List.ofFn_zero,List.prod_nil,mul_one] using hg
    exact hg'.symm ▸ m.property
  let i : Fin r := ⟨0,hrpos⟩
  let L := (K i).map N.subtype
  have hL : IsChiZeroBlockIn L := chiZero_map_normal_subgroup N (K i) (hK i)
  have hLo : ¬L ≤ M := fun h => hout i (map_le_iff_le_comap.mp h)
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup N)).map N.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,hS]
    exact elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) _
      (elementaryAbelianMaxJ_le_baumann _) inf_le_left
  have hmove : L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hh := congrArg (map N.subtype) (hm i)
    rwa [map_commutator,hJmap] at hh
  refine ⟨L,hL,hmove,?_,hLo⟩
  by_contra hh
  have hle := hP.1.le_maximal
    ⟨(minimalParabolicMax_spec T hP).2,(minimalParabolicMax_spec T hP).1.covBy_top⟩
    (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right) (lt_top_iff_ne_top.mpr hh)
  exact hLo (le_sup_left.trans hle)
end CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
