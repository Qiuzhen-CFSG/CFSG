module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Subtype

/-!
# Fixed-pair C.1.28 for the original single-factor solvable action

Select a minimal parabolic escaping the original control subgroup and retain
the full Sylow subgroup. Transport the same universal pair along the actual
Baumann inclusion; escape makes its local control proper. The local cubic
source and ambient lift then construct a moving A₃ block of the original group.
All selection, pair, subnormality and module-support premises are discharged.

This is the single-factor source implication used by 14.1.11. The quotient
action is solvable with abelian Sylow image; its kernel need not be a two-group.
Source: Aschbacher--Smith C.1.28 and 14.1.11, printed pp.133,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem exists_moving_alternatingThree_of_fixed_pair_escape
    (T : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hproper : control T D ≠ ⊤) (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (habel : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))))) :
    ∃ A : Subgroup G, IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅normalClosure
        (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ∧
      ⁅normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G),A⁆ ≠ ⊥ := by
  obtain ⟨H,hTH,hP,hout⟩ := exists_minimalParabolic_outside T D hproper
  exact ⟨(pResidual 2 H).map H.subtype,
    ambient_alternatingThree_of_single_minimal_escape T hfit hrank hsolv habel H hTH hP
      (subtypePair T D H hTH) (subtypePair_universal T D hD H hTH)
      (subtypePair_control_ne_top T D H hTH hout)⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
