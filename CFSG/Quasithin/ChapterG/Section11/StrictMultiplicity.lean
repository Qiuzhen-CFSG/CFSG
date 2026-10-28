module

public import CFSG.Quasithin.ChapterG.Section11.Transvection
public import CFSG.Quasithin.ChapterG.Section11.StrictSmallCases

/-!
# The low-rank constituent reduction on the strict quotient

Apply the marked multiplicity argument to the literal point-centralizer
quotient acting on U/Z(U), retaining its crossing image and relative crossing
center. The supplied ambient Sylow fixes the marked point and contains the
crossing image normally, exactly as in G.11.1(4).

In the nonsolvable marked branch the actual component orbit acts either
irreducibly or as two isomorphic simple copies. In the latter case the
original witness has rank one on each copy, and G.6.4 classifies its literal
constituent action quotient. This removes higher multiplicity from the strict
classification step; the remaining model recognition and
source-hypothesis construction are still required.

Source: Aschbacher--Smith G.10.16(4), G.11.8 and 6.2.18(2), printed
pp.363--364,368,690.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  (T L R : Subgroup G) (z d : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  [IsElementaryAbelian 2 (strictCrossingImage T L R z d)]

/-- The actual strict quotient satisfies the refined G.11 reduction, with
relative Sylow normality and the exact low-rank witness supplied explicitly. -/
theorem strict_conclusion_or_component_reduction
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (v : Additive (StrictVectorQuotient T L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (StrictActor T L R z)))
    (a : StrictActor T L R z) (ha : a ∈ strictCrossingImage T L R z d)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace (strictRepresentation T L R z) a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace (strictRepresentation T L R z) a)
    (S : Sylow 2 (StrictActor T L R z))
    (hSv : (S : Subgroup (StrictActor T L R z)) ≤
      ChapterG.Section10.pointCentralizer (strictRepresentation T L R z) v)
    (hXS : strictCrossingImage T L R z d ≤ S)
    (hXn : ((strictCrossingImage T L R z d).subgroupOf
      (S : Subgroup (StrictActor T L R z))).Normal) :
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) ∨
      (IsIrreducible (strictRepresentation T L R z) ∧
        6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) ∧
        ((Group.IsSolvable (StrictActor T L R z) ∧
            finrank (ZMod 2) (Additive (strictCrossingImage T L R z d)) = 2 ∧
            finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) = 6) ∨
          (¬ Group.IsSolvable (StrictActor T L R z) ∧
            ChapterG.Section11.ComponentReduction (strictRepresentation T L R z) B v
              (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
              (strictCrossingImage T L R z d)))) :=
  ChapterG.Section11.conclusion_or_component_reduction h cover ⟨a,ha,hr,hv⟩ ⟨S,hSv,hXS,hXn⟩

/-- In the proper marked branch of the same strict action, G.6.4 classifies
the literal constituent action quotient, with no recognition premise. -/
theorem strict_proper_marked_constituent_rankOne_classification
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (v : Additive (StrictVectorQuotient T L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (StrictActor T L R z)))
    (a : StrictActor T L R z) (ha : a ∈ strictCrossingImage T L R z d)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace (strictRepresentation T L R z) a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace (strictRepresentation T L R z) a)
    (hS : ChapterG.Section11.NormalSylow (strictRepresentation T L R z) v
      (strictCrossingImage T L R z d))
    (hn : ¬ Group.IsSolvable (StrictActor T L R z))
    (K : Subgroup (StrictActor T L R z)) (hK : Theory.GroupTheory.IsComponent _ K)
    (hm : ⁅K,strictCrossingImage T L R z d⁆ ≠ ⊥)
    (I : Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (hI : BinaryOffender.IsIrrPlus (strictRepresentation T L R z) (componentOrbit K ⊤) I)
    (hvI : v ∈ I) (hp : I ≠ ⊤) :
    let ρ := strictRepresentation T L R z
    let X := strictCrossingImage T L R z d
    let H := componentOrbit K ⊤
    letI := Theory.GroupTheory.componentOrbit_top_normal K
    let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hvI
    let σ := ChapterG.Section09.constituentAction ρ H X I hI.choose hXI
    ∃ b : X, orderOf (b : StrictActor T L R z) = 2 ∧ v ∈ RankTwo.movedSpace ρ b ∧
      finrank (ZMod 2) (RankTwo.movedSpace ρ b) = 2 ∧
      let bP : (H ⊔ X : Subgroup (StrictActor T L R z)) :=
        ⟨b,(le_sup_right : X ≤ H ⊔ X) b.property⟩
      finrank (ZMod 2) (LinearMap.range (σ bP - LinearMap.id)) = 1 ∧
      ChapterG.Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker bP) :=
  ChapterG.Section11.proper_marked_constituent_rankOne_classification h cover
    ⟨a,ha,hr,hv⟩ hS hn hK hm hI hvI hp

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
