module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.GraphCentralizer
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PointDerived
public import Theory.GroupTheory.DerivedCentralizerFusion

/-!
# Excluding fusion of the marked unitary graph and root involutions

The explicit fixed-endpoint words give a nonidentity cubic in the second
derived subgroup of the marked graph centralizer. In contrast, the actual
extended point endpoint has a two-group second derived subgroup. If the graph
involution were fused to the source root involution, the source centralizer
bound would embed its centralizer into this point endpoint, a contradiction.

The point-group assertion and the fixed words are both proved for the
literal models. No centralizer recognition or nonfusion premise remains.
This is the marked-graph instance of Aschbacher--Smith F.4.36, printed p.292;
the full graph-class placement and the exceptional F.5 analysis are separate.
-/
public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.GraphFusion
open Subgroup GreenBook.LieModels.UnitaryFour GraphCentralizer
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The original centralizer bound alone excludes fusion of the actual
marked graph involution to the root element in a faithful completion. -/
theorem source_marked_graph_not_conjugate_root
    (hi : Function.Injective i)
    (z : Extension.point 1 hn)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    ¬ IsConj (i (c.middle graphInvolution)) (i (c.left z)) :=
  Theory.GroupTheory.not_isConj_of_derivedCentralizer 2 2
    (i.comp c.left) (hi.comp c.left_injective)
    (graphCentralizer_not_two_group_second_derived c i hi) hc
    Extension.binary_point_secondDerived_isTwoGroup

/-- The entire ambient conjugacy class of the marked graph involution
is disjoint from the source root class. -/
theorem source_graph_class_not_conjugate_root
    (hi : Function.Injective i)
    (z : Extension.point 1 hn)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    {x : G} (hx : IsConj (i (c.middle graphInvolution)) x) :
    ¬ IsConj x (i (c.left z)) :=
  fun h => source_marked_graph_not_conjugate_root c i hi z hc (hx.trans h)

/-- In particular the marked graph element is distinct from every root
conjugate in the same actual ambient group. -/
theorem source_root_class_not_conjugate_graph
    (hi : Function.Injective i)
    (z : Extension.point 1 hn)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    {x : G} (hx : IsConj (i (c.left z)) x) :
    ¬ IsConj x (i (c.middle graphInvolution)) :=
  fun h => source_marked_graph_not_conjugate_root c i hi z hc (hx.trans h).symm

end CFSG.Quasithin.ChapterF.UnitaryTwo.GraphFusion
