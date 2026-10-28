module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Rank-two E-generation of the Hall--Janko first-local quotients

The actual alternating subgroup is the simple generalized Fitting subgroup
of S₅. Its quotient has order two, so a Sylow two-subgroup supplements it.
The whole-group E2 theorem and the proved two-rank bound therefore give
rank-two E-generation. The same argument applies to A₅ itself. In both
cases the local tau, solvable radical and two-residual are those in the
source definitions. No general generation-existence premise is used.

These bounds are lifted through the concrete J₂ first parabolics' intrinsic
two-cores in `LocalGeneration`. Source: Aschbacher--Smith E.1.2, E.1.5,
E.1.12 and E.1.14(5), printed pp.210, 214; Aschbacher (1982), Lemma 4.9.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoTwo

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
open Sporadic.Mathieu.M22ValueBound.SmallQuotients

private theorem five_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) := by
  rw [← symmetricFive_generalizedFitting_eq_alternating]
  exact symmetricFive_generalizedFitting_isQuasisimple

private theorem bound_of_simple_fitting {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G))
    (hq : IsPGroup 2 (G ⧸ generalizedFitting G))
    (hr : primeRank 2 G ≤ 2) : IsEGenerated 2 G := by
  intro T
  apply isEGeneratedAt_of_top_component_and_rank T
  · intro A _ _ hne
    exact eCaseComponent_top ha T
      (by simpa only [sup_comm] using T.sup_eq_top_of_quotient_isPGroup _ hq) _ A hne
  · intro A hA _
    let := hA
    exact (A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)).trans hr

theorem symmetric_five_isEGenerated : IsEGenerated 2 (Equiv.Perm (Fin 5)) := by
  have hF := symmetricFive_generalizedFitting_eq_alternating
  let : IsSimpleGroup (generalizedFitting (Equiv.Perm (Fin 5))) := by
    rw [hF]
    exact alternatingGroup.isSimpleGroup (by simp)
  let := symmetricFive_generalizedFitting_isQuasisimple
  have : Nontrivial (generalizedFitting (Equiv.Perm (Fin 5))) := inferInstance
  apply bound_of_simple_fitting
    (Group.IsPerfect.not_isMulCommutative _) _ symmetricFive_primeRank_le_two
  have hq : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) :=
    IsPGroup.of_card (n := 1) alternatingGroup.index_eq_two
  exact hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hF).symm

theorem alternating_five_isEGenerated : IsEGenerated 2 (alternatingGroup (Fin 5)) := by
  let := five_quasisimple
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hF : generalizedFitting (alternatingGroup (Fin 5)) = ⊤ :=
    generalizedFitting_eq_top_of_quasisimple
  let d : generalizedFitting (alternatingGroup (Fin 5)) ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  let : IsSimpleGroup (generalizedFitting (alternatingGroup (Fin 5))) := d.isSimpleGroup
  let : IsQuasisimple (generalizedFitting (alternatingGroup (Fin 5))) :=
    IsQuasisimple.of_mulEquiv d.symm
  apply bound_of_simple_fitting (Group.IsPerfect.not_isMulCommutative _) _
    ((primeRank_le_of_injective 2 (alternatingGroup (Fin 5)).subtype
      (alternatingGroup (Fin 5)).subtype_injective).trans symmetricFive_primeRank_le_two)
  have hq : IsPGroup 2
      (alternatingGroup (Fin 5) ⧸ (⊤ : Subgroup (alternatingGroup (Fin 5)))) :=
    IsPGroup.of_card (n := 0) Subgroup.index_top
  exact hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hF).symm

end CFSG.Quasithin.ChapterE.JankoTwo
