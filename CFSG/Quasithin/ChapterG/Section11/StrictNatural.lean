module
public import CFSG.Quasithin.ChapterG.Section11.NaturalConstituent
public import CFSG.Quasithin.ChapterG.Section11.StrictMultiplicity

/-!
# The remaining natural constituent rows on the strict quotient

Apply the full-linear and two-factor exclusions to the original strict action
in 6.2.18(2). Every proper marked branch either gives the full G.11.2 conclusion
or has the actual doubled A₆, A₇ or A₈ natural action on its component orbit.
The strict vector quotient, form, crossing image, smaller crossing center,
marked low-rank witness and relative Sylow normality are unchanged.

Source: Aschbacher--Smith G.10.16(4), G.11.6--8 and 6.2.18(2),
printed pp.363--368,690. Whole-group recognition of the remaining natural
rows, and the other source branches, are still required for G.11.2.
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
theorem strict_conclusion_or_natural_component_reduction
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
            ChapterG.Section11.NaturalComponentReduction (strictRepresentation T L R z) B v
              (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
              (strictCrossingImage T L R z d)))) :=
  ChapterG.Section11.conclusion_or_natural_component_reduction h cover ⟨a,ha,hr,hv⟩ ⟨S,hSv,hXS,hXn⟩

/-- The actual component-orbit action in the proper marked strict branch is
identified on the whole module, including its exact dimension. -/
theorem strict_proper_marked_constituent_natural_actions
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
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) ∨
      ∃ n, 6 ≤ n ∧ n ≤ 8 ∧
        ChapterG.Section09.Quasiequivalent
          ((strictRepresentation T L R z).comp (componentOrbit K ⊤).subtype)
          ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
            (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ∧
        ((n = 6 ∧ finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) = 8) ∨
          ((n = 7 ∨ n = 8) ∧
            finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) = 12)) :=
  ChapterG.Section11.proper_marked_constituent_natural_actions h cover
    ⟨a,ha,hr,hv⟩ hS hn hK hm hI hvI hp

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
