module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore

/-!
# Commutator generation of the HS pair kernel

Two explicit elements of the alternating preimage generate the whole pair
kernel through their commutators with its five existing word witnesses.
Writing a,b for the ATLAS generators and g = b²ab, the actors are the fourth
power of g(e0 g⁻¹ e0 g)² and its conjugate by s1. Both belong to the
alternating preimage because their signs are trivial. Five short identities
put the two quaternion pairs and the cyclic generator in [core,modelResidual].
`model_core_expression` then gives the full subgroup equality.

A packed permutation is proved equal to the carrier word once, so the later
identities reduce only short table expressions. All calculations are checked
by Lean's kernel. `source/discover.py` reproduces the small certificates;
it is not a proof oracle. ATLAS attribution and conventions are inherited
from `EvenLocalCandidates` and `CentralInvolutionCore`.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423;
the underlying core structure is 16.1.5(10), printed p.1172.
-/

public section
open Subgroup
open scoped commutatorElement
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
set_option maxRecDepth 10000

private def letterA : Carrier := ⟨ab0, by
  rw [ab0_eq]
  exact Subgroup.subset_closure (by simp)⟩

private def letterB : Carrier := ⟨ab1, by
  rw [ab1_eq]
  exact Subgroup.subset_closure (by simp)⟩

private def seed : Carrier := letterB ^ 2 * letterA * letterB

private def actorWord : Carrier := seed * (e0 * seed⁻¹ * e0 * seed) ^ 2

private def actorMap (i : Fin 100) : Fin 100 :=
  ⟨(3428552545602081022243410960445654748807388865485707366179205922790529746047938661191030246204643399099225979979366433827744722504290555873612332160545260607726212080695948742285872813782326474851282089742278467 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def actorInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3064039531095635151665397980982787874147390246448009519785485584603188759357265404038720608556443486775018332538383274826591347421161865920669565924310396630935361132252990043139775044404920089232700636438825260 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem actor_left : ∀ i, actorInvMap (actorMap i) = i := by
  apply allFin
  decide +kernel

private def actorPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm actorMap actorInvMap actor_left
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin actor_left)

private theorem actor_word : actorPerm = actorWord.val := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def actor : Carrier := ⟨actorPerm, actor_word.symm ▸ actorWord.property⟩

private theorem actor_commutes : actor * e0 = e0 * actor := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s1_commutes : s1 * e0 = e0 * s1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private def inLocal (g : Carrier) (hg : g * e0 = e0 * g) : localGroup 0 :=
  ⟨g, by rw [localGroup_zero_eq_centralizer]; exact mem_centralizer_singleton_iff.mpr hg⟩

private def actorLocal : localGroup 0 := (inLocal actor actor_commutes) ^ 4

private def swapLocal : localGroup 0 := inLocal s1 s1_commutes

private def actorConj : localGroup 0 := swapLocal * actorLocal * swapLocal⁻¹

private theorem leftI_comm : leftI.val = ⁅(qElement 0).val, actorConj⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem leftJ_comm : leftJ.val = ⁅(qElement 1).val, actorConj⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem rightI_comm : rightI.val =
    ⁅(qElement 2).val, actorConj⁆ * ⁅(qElement 3).val, actorLocal⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem rightJ_comm : rightJ.val = ⁅(qElement 2).val, actorConj⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem cyclicGenerator_comm : cyclicGenerator.val =
    ⁅(qElement 2).val, actorLocal⁆ * ⁅(qElement 4).val, actorConj⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- Normality is in the full representative local group. -/
instance modelResidual_normal : modelResidual.Normal := inferInstanceAs
  ((alternatingGroup (Fin 5)).comap CentralNormalizerThreePart.PairQuotient.fiveHom).Normal

/-- The pair kernel lies in the alternating preimage. -/
theorem model_core_le_residual : core ≤ modelResidual := by
  intro x hx
  change CentralNormalizerThreePart.PairQuotient.fiveHom x ∈ alternatingGroup (Fin 5)
  have h : CentralNormalizerThreePart.PairQuotient.fiveHom x = 1 := by
    rwa [← MonoidHom.mem_ker, CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
  rw [h]
  exact one_mem _

/-- The sign of the five-point action kills every square. -/
theorem modelResidual_square_mem (x : localGroup 0) : x ^ 2 ∈ modelResidual := by
  change CentralNormalizerThreePart.PairQuotient.fiveHom (x ^ 2) ∈ alternatingGroup (Fin 5)
  rw [Equiv.Perm.mem_alternatingGroup, map_pow, map_pow, Int.units_sq]

private theorem actorLocal_mem : actorLocal ∈ modelResidual := by
  simpa only [actorLocal, ← pow_mul] using
    modelResidual.pow_mem (modelResidual_square_mem (inLocal actor actor_commutes)) 2

private theorem actorConj_mem : actorConj ∈ modelResidual :=
  (inferInstance : modelResidual.Normal).conj_mem _ actorLocal_mem swapLocal

private theorem core_le_of_generators (U : Subgroup (localGroup 0))
    (hi : leftI.val ∈ U) (hj : leftJ.val ∈ U)
    (hk : rightI.val ∈ U) (hl : rightJ.val ∈ U)
    (hz : cyclicGenerator.val ∈ U) : core ≤ U := by
  intro g hg
  obtain ⟨a, b, c, he⟩ := model_core_expression ⟨g, hg⟩
  have ha : (leftEmbedding a).val ∈ U := by
    cases a with
    | a n => exact U.pow_mem hi n.val
    | xa n => exact U.mul_mem hj (U.pow_mem hi n.val)
  have hb : (rightEmbedding b).val ∈ U := by
    cases b with
    | a n => exact U.pow_mem hk n.val
    | xa n => exact U.mul_mem hl (U.pow_mem hk n.val)
  have hc : (cyclicEmbedding c).val ∈ U := U.pow_mem hz c.toAdd.val
  have h := U.mul_mem (U.mul_mem ha hb) hc
  change (leftEmbedding a * rightEmbedding b * cyclicEmbedding c).val ∈ U at h
  rwa [he] at h

/-- The full core, including its cyclic factor, is generated by its commutators
with the alternating preimage. This discharges the source equality R* = [R*,X*]. -/
theorem model_core_commutator : ⁅core, modelResidual⁆ = core := by
  let := core_normal
  apply le_antisymm (commutator_le_left _ _)
  apply core_le_of_generators
  · rw [leftI_comm]
    exact commutator_mem_commutator (qElement 0).property actorConj_mem
  · rw [leftJ_comm]
    exact commutator_mem_commutator (qElement 1).property actorConj_mem
  · rw [rightI_comm]
    exact mul_mem
      (commutator_mem_commutator (qElement 2).property actorConj_mem)
      (commutator_mem_commutator (qElement 3).property actorLocal_mem)
  · rw [rightJ_comm]
    exact commutator_mem_commutator (qElement 2).property actorConj_mem
  · rw [cyclicGenerator_comm]
    exact mul_mem
      (commutator_mem_commutator (qElement 2).property actorLocal_mem)
      (commutator_mem_commutator (qElement 4).property actorConj_mem)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
