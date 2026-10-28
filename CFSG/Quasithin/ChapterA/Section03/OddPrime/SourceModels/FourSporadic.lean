module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.ThreeSubgroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupAction.ComponentRankAction.OuterTwo
/-!
# Cubic rank and residuals for the four sporadic completion rows

The concrete J₂ and HS rank witnesses give elementary nines. The certified
nonabelian subgroups of order 27 in J₄ and Ru give cubic rank at least two:
otherwise their odd Sylow groups would be cyclic. The established outer
calculations give two-groups in every row, with Ru simplicity inherited
from the actual centerless quasisimple component.

The final theorem applies A.3.18 to that original component and its literal
three-residual. It supplies the four sporadic cases needed in both residual
calculations of 14.2.15; component placement in the later local group is
separate from this model calculation.

Source: Aschbacher--Smith A.3.18, pp.51--53, and 14.2.15, pp.985--986.
The imported concrete subgroup and outer calculations retain their ATLAS
and GLS3 source attributions.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic

private theorem nonabelian_three_subgroup_rank
    {B : Type*} [Group B] [Finite B] (P : Subgroup B)
    (hc : Nat.card P = 3^3) (hna : ¬IsMulCommutative P) :
    2 ≤ primeRank 3 B := by
  have hP : IsPGroup 3 P := IsPGroup.of_card hc
  have hr : 2 ≤ primeRank 3 P := by
    by_contra hn
    have hone : primeRank 3 P ≤ 1 := by omega
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => by
        let : IsElementaryAbelian 3 E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hone E)
    exact hna inferInstance
  exact hr.trans (primeRank_subgroup_le 3 P)

/-- The actual J₄ carrier has a noncyclic cubic Sylow subgroup. -/
theorem j4_three_rank_ge_two : 2 ≤ primeRank 3 Janko4.Model := by
  exact nonabelian_three_subgroup_rank
    (Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (Janko4.Simplicity.threeLocal_card _ _) (Janko4.Simplicity.threeLocal_not_isMulCommutative _ _)

/-- The actual Ru carrier has a noncyclic cubic Sylow subgroup. -/
theorem rudvalis_three_rank_ge_two : 2 ≤ primeRank 3 Rudvalis.Model := by
  obtain ⟨P,hc,hn⟩ := MainConverse.SporadicLocal.RuRank.three_subgroup
  exact nonabelian_three_subgroup_rank P hc hn

private theorem transport_three_outer
    {L B : Type*} [Group L] [Finite L] [Group B] [Finite B]
    (e : L ≃* B) (hr : 2 ≤ primeRank 3 B) (ho : IsPGroup 2 (MulAut.Outer B)) :
    2 ≤ primeRank 3 L ∧ IsPGroup 2 (MulAut.Outer L) := by
  refine ⟨?_,ho.of_equiv (MulAut.outerCongr e).symm⟩
  rwa [primeRank_equiv 3 e]

/-- The four actual sporadic markings supply both A.3.18 model inputs. -/
theorem three_rank_and_outer_two
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hz : center L = ⊥)
    (he : Nonempty (L ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (L ≃* Janko4.Model) ∨
      Nonempty (L ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (L ≃* Rudvalis.Model)) :
    2 ≤ primeRank 3 L ∧ IsPGroup 2 (MulAut.Outer L) := by
  rcases he with he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact transport_three_outer e Sporadic.LeechRelated.J2.three_rank_ge_two
      Sporadic.LeechRelated.J2.outer_isTwoGroup
  · exact transport_three_outer e j4_three_rank_ge_two Janko4.AdequateLocal.outer_isPGroup_two
  · exact transport_three_outer e Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
      (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
  · let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let ez : (L ⧸ center L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    let : IsSimpleGroup L := ez.symm.isSimpleGroup
    let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
    let := Chapter1.XiEmbedding.OuterModels.rudvalis_outer_subsingleton
    exact transport_three_outer e rudvalis_three_rank_ge_two (IsPGroup.of_subsingleton 2 _)
/-- The cubic residual is the original component in each of the four rows. -/
theorem component_eq_primeClosure_and_residual
    {G : Type*} [Group G] [Finite G]
    (hG : primeRank 3 G ≤ 2) {L : Subgroup G} (hL : IsComponent G L)
    (hz : center L = ⊥)
    (he : Nonempty (L ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (L ≃* Janko4.Model) ∨
      Nonempty (L ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (L ≃* Rudvalis.Model)) :
    L = closure {x : G | orderOf x = 3} ∧ L = primeToResidual 3 G := by
  let := hL.2
  obtain ⟨hr,ho⟩ := three_rank_and_outer_two hz he
  let e : (L ⧸ center L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hL (by rw [hz]; simp) hr hG e (by decide) ho

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic
