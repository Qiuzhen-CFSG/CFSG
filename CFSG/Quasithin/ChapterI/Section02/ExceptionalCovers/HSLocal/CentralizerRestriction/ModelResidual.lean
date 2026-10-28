module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelResidual.Commutators
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The actual HS centralizer residual and its core action

The alternating preimage in the five-point action is perfect: its commutator
contains the pair kernel and maps onto A₅. Its quotient in the full local has
exponent two, so it is precisely O² of that local. Normality identifies its
intrinsic two-core with the same pair kernel. The existing action and quotient
from `ModelCore` retain their literal representatives and exact kernel.

Finally `localGroup_zero_eq_centralizer` identifies the residual and embedded
core of the actual representative centralizer in HS. These equations discharge
the residual and core-action premises in the exceptional-cover argument;
transport to arbitrary covers remains with the parent assembly.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

public section
open Subgroup
open scoped commutatorElement
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

/-- The intrinsic two-core of the alternating preimage is the original pair kernel. -/
theorem modelResidual_pCore_eq : pCore 2 modelResidual = core.subgroupOf modelResidual := by
  apply le_antisymm
  · have h : (pCore 2 modelResidual).map modelResidual.subtype ≤ pCore 2 (localGroup 0) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map modelResidual.subtype⟩
    rw [model_pCore_eq] at h
    intro x hx
    exact h (mem_map_of_mem _ hx)
  · exact le_sSup ⟨inferInstance, core_isPGroup.comap_subtype⟩

/-- Core commutator generation and the perfect A₅ quotient give perfection. -/
instance modelResidual_isPerfect : Group.IsPerfect modelResidual := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_left _ _)
  have hc : core ≤ ⁅modelResidual, modelResidual⁆ := by
    rw [← model_core_commutator]
    exact commutator_mono model_core_le_residual le_rfl
  have himage : modelResidual.map CentralNormalizerThreePart.PairQuotient.fiveHom =
      alternatingGroup (Fin 5) := by
    exact map_comap_eq_self (by rw [MonoidHom.range_eq_top_of_surjective _
      CentralNormalizerThreePart.PairQuotient.fiveHom_surjective]; exact le_top)
  have hm : modelResidual.map CentralNormalizerThreePart.PairQuotient.fiveHom ≤
      ⁅modelResidual, modelResidual⁆.map CentralNormalizerThreePart.PairQuotient.fiveHom := by
    rw [map_commutator, himage, commutator_alternatingGroup_eq_self (by simp)]
  have hh := map_le_map_iff.mp hm
  rwa [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel, sup_eq_left.mpr hc] at hh

private theorem modelResidual_quotient_isTwoGroup : IsPGroup 2 ((localGroup 0) ⧸ modelResidual) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective modelResidual x
  refine ⟨1, ?_⟩
  rw [pow_one, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (modelResidual_square_mem g)

/-- The actual O² of the full representative local is the alternating preimage. -/
theorem model_pResidual_eq : pResidual 2 (localGroup 0) = modelResidual := by
  apply pResidual_eq_of_isPPerfect modelResidual ?_ modelResidual_quotient_isTwoGroup
  intro N hN hq
  let := hN
  by_contra hne
  let : Nontrivial (modelResidual ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (modelResidual ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (modelResidual ⧸ N) inferInstance

open Theory.GroupTheory

/-- Identification in the original HS carrier, using the actual representative centralizer. -/
theorem marked_centralizer_residual_eq :
    centralizerTwoResidual e0 = modelResidual.map (localGroup 0).subtype := by
  unfold centralizerTwoResidual
  rw [← localGroup_zero_eq_centralizer, model_pResidual_eq]

/-- The embedded O₂(O²(C_HS(e0))) is exactly the embedded pair kernel. -/
theorem marked_centralizer_core_eq :
    centralizerCore e0 = core.map (localGroup 0).subtype := by
  change (centralizerTwoResidual e0).pCoreIn 2 = _
  rw [marked_centralizer_residual_eq, ← map_pCoreIn_of_injective 2 modelResidual
    (localGroup 0).subtype (localGroup 0).subtype_injective, pCoreIn, modelResidual_pCore_eq,
    map_subgroupOf_eq_of_le model_core_le_residual]

/-- The source commutator equation in the actual HS carrier. -/
theorem marked_centralizer_core_commutator :
    ⁅centralizerCore e0, centralizerTwoResidual e0⁆ = centralizerCore e0 := by
  rw [marked_centralizer_core_eq, marked_centralizer_residual_eq,
    ← map_commutator, model_core_commutator]

/-- Perfection of the actual representative centralizer residual. -/
theorem marked_centralizer_residual_perfect : Group.IsPerfect (centralizerTwoResidual e0) := by
  rw [marked_centralizer_residual_eq]
  exact Group.IsPerfect.map _

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
