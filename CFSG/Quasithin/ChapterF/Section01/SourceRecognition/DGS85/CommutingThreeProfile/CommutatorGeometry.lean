module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionGeometry
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import FeitThompson.ChiefFactors.Core
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The intersection commutator in DGS 12.3

The displayed decomposition of the middle core on p.180, together with
[ V_x,Q_x ] <= Z_x and [ V_y,Q_y ] <= Z_y, bounds [ V_x intersect V_y,Q_m ]
by Z_m. Relative minimality of the natural center gives exactly the source
dichotomy: this commutator is Z_m, or the intersection centralizes Q_m.
The latter alternative is deliberately retained.

Local transitivity expresses the actual V_y as Z_y joined with the orbit
span of one neighboring center. Consequently the noncentral intersection
alternative and the earlier [V_y,Q_y]=Z_y imply [V_y,L_y]=V_y. This proves
the last generation step of (12.3)(d) without identifying L_y with a starred
endpoint or omitting the center at y.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (12.3), printed pp.179--180. The core-product calculation and the
central-case exclusion remain local Chapter 12 obligations. Minimality of
Z_m is the irreducibility part of the preceding natural-module assertion
(12.1)(e), owned with Chapter 8. The reduced source applications are in
`GeneratedIntersection`.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G) [∀ i, Finite (F i)]

/-- The second displayed core product on p.180 bounds the intersection commutator. -/
theorem intersection_commutator_le_center {x y m : Vertex F}
    (hx : ⁅V F x 1, Q F x⁆ ≤ Z F x) (hy : ⁅V F y 1, Q F y⁆ ≤ Z F y)
    (hzx : Z F x ≤ Z F m) (hzy : Z F y ≤ Z F m)
    (hprod : Q F m = (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)) :
    ⁅V F x 1 ⊓ V F y 1, Q F m⁆ ≤ Z F m := by
  have hn : Q F m ≤ normalizer (Z F m : Set G) := (Q_le_stabilizer F m).trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F m)).mp (Z_normal F m))
  rw [commutator_comm, hprod]
  apply commutator_sup_le_of_relative_normal (Q F m) _ _ _ _ hn inf_le_right inf_le_right
  · rw [commutator_comm]
    exact ((commutator_mono inf_le_left inf_le_left).trans hx).trans hzx
  · rw [commutator_comm]
    exact ((commutator_mono inf_le_right inf_le_left).trans hy).trans hzy

omit [∀ i, Finite (F i)] in
/-- Relative minimality of the actual natural center yields the precise p.180 dichotomy. -/
theorem intersection_commutator_dichotomy {x y m : Vertex F}
    (A : Subgroup G) (hA : A ≤ stabilizer F m)
    (hZA : Z F m ≤ A)
    (hNA : A ≤ normalizer (V F x 1 ⊓ V F y 1 : Set G))
    (hbound : ⁅V F x 1 ⊓ V F y 1, Q F m⁆ ≤ Z F m)
    [hnZ : ((Z F m).subgroupOf A).Normal]
    [IsMinimalNormal ((Z F m).subgroupOf A)] :
    ⁅V F x 1 ⊓ V F y 1, Q F m⁆ = Z F m ∨
      V F x 1 ⊓ V F y 1 ≤ centralizer (Q F m : Set G) := by
  let D := ⁅V F x 1 ⊓ V F y 1, Q F m⁆
  have hDA : D ≤ A := hbound.trans hZA
  have hnQ : A ≤ normalizer (Q F m : Set G) :=
    hA.trans ((stabilizer F m).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F m))))
  have hnD : A ≤ normalizer (D : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hNA hg),
      mem_normalizer_iff_map_conj_eq.mp (hnQ hg)]
  let : (D.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnD
  rcases IsMinimalNormal.minimal (H := (Z F m).subgroupOf A) (D.subgroupOf A)
      (subgroupOf_mono A hbound) with he | he
  · right
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hm := congrArg (Subgroup.map A.subtype) he
    simpa only [map_subgroupOf_eq_of_le hDA, Subgroup.map_bot] using hm
  · left
    have hm := congrArg (Subgroup.map A.subtype) he
    simpa only [map_subgroupOf_eq_of_le hDA,
      map_subgroupOf_eq_of_le hZA] using hm


/-- A transitive local group generates the literal closed-ball span from one
neighboring center and the center at the base vertex. -/
theorem V_eq_center_sup_neighbor_conjugates {y m : Vertex F}
    (A : Subgroup G) (hA : A ≤ stabilizer F y) (hadj : (graph F).Adj y m)
    (htrans : ∀ z, (graph F).Adj y z → ∃ g ∈ A, g • m = z) :
    V F y 1 = Z F y ⊔ conjugateSpanBy (Z F m) A := by
  have hm : Z F m ≤ V F y 1 :=
    le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hadj)) le_rfl)
  apply le_antisymm
  · apply iSup_le
    intro z
    apply iSup_le
    intro hz
    rcases (mem_ball_one F y z).mp hz with hz | rfl
    · obtain ⟨g, hg, hgm⟩ := htrans z hz
      rw [← hgm, Z_translate F]
      apply le_trans _ le_sup_right
      rintro a ⟨b, hb, rfl⟩
      exact subset_closure ⟨g, hg, b, hb, rfl⟩
    · exact le_sup_left
  · exact sup_le (Z_le_V F y 1)
      (conjugateSpanBy_le hm (hA.trans (stabilizer_normalizes_V F y 1)))

/-- DGS 12.3(d) follows from the noncentral alternative in 12.3(c), with the
same local group and the actual neighboring center span. -/
theorem V_eq_commutator_of_intersection {x y m : Vertex F}
    (A : Subgroup G) (hA : A ≤ stabilizer F y) (hadj : (graph F).Adj y m)
    (htrans : ∀ z, (graph F).Adj y z → ∃ g ∈ A, g • m = z)
    (hQy : Q F y ≤ A) (hQm : Q F m ≤ A)
    (hy : ⁅V F y 1, Q F y⁆ = Z F y)
    (hc : ⁅V F x 1 ⊓ V F y 1, Q F m⁆ = Z F m) : V F y 1 = ⁅V F y 1, A⁆ := by
  have hnV := hA.trans (stabilizer_normalizes_V F y 1)
  have hn : A ≤ normalizer (⁅V F y 1, A⁆ : Subgroup G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnV hg),
      mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer hg)]
  apply le_antisymm _ (le_normalizer_iff_commutator_le_left.mp hnV)
  conv_lhs => rw [V_eq_center_sup_neighbor_conjugates F A hA hadj htrans]
  apply sup_le
  · rw [← hy]
    exact commutator_mono le_rfl hQy
  · apply conjugateSpanBy_le _ hn
    rw [← hc]
    exact commutator_mono inf_le_right hQm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
