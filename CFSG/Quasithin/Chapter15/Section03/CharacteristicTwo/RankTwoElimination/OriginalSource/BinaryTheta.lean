module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Source
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import Theory.GroupTheory.PResidual.QuasisimpleCubicGeneration
public import Theory.SpecificGroups.BinaryComponentResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Commutator
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# The ordinary cubic residual for the binary components

The actual four- and five-dimensional binary quotients have trivial center,
three-rank two, and two-group outer automorphisms. The rank-two C-component
residual theorem and intrinsic cubic generation identify L with theta(I).
The original local theta identity then places Yplus in L.

Source: Aschbacher–Smith 15.3.17(2), printed p.1126.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- In the ordinary rank-two case the actual component is the cubic residual
of I; its perfectness then gives the source equality L=theta(I). -/
theorem component_eq_theta_of_ordinary_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hrI : primeRank 3 I ≤ 2)
    (hfacts : Facts (c.L ⧸ pCore 2 c.L)) : c.L = theta I := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hK : K.IsCComponent := LocalData.thompson_component_in c.le_thompson c.component
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hF := Facts.of_equiv b hfacts
  have hres : c.L.subgroupOf I = primeToResidual 3 I :=
    hK.eq_primeToResidual_three_of_rank_outer_two hF.1 hF.2.1 hrI hF.2.2
  have hr : 2 ≤ primeRank 3 c.L := hfacts.2.1.trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hz : primeRank 3 (center (c.L ⧸ pCore 2 c.L)) ≤ 1 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n := 1)
    rw [hfacts.1,card_bot]
    decide
  exact (cubic_closure_eq_of_primeToResidual c.L I (component_le c) hr hz hres).symm

/-- The ordinary quotient facts apply to both surviving higher-dimensional
binary projective models, using their actual central quotients. -/
theorem component_eq_theta_of_binary_four_five
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hrI : primeRank 3 I ≤ 2) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) : c.L = theta I := by
  apply component_eq_theta_of_ordinary_quotient d c hrI
  exact Facts.of_equiv (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)))
    (Theory.SpecificGroups.BinaryComponentResidual.linear hn)

/-- The part of 15.3.17(2) needed by 15.3.24, from the original selection
hypotheses and the specified four- or five-dimensional quotient. -/
theorem source_lemma_15_3_17_binary_four_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)) :
    d.Yplus ≤ c.L ∧ c.L = theta I := by
  have he := component_eq_theta_of_binary_four_five d c
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin
      3 Nat.prime_three (by decide)) hn e
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  refine ⟨?_,he⟩
  rw [h11.theta_eq,he]
  exact theta_mono inf_le_right

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
