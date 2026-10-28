module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Checked
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Interpretation
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Checked
public import Theory.GroupTheory.PairedWordCover

/-! The synchronized native/projective Schreier cover bounds the paired group by300·13·2=7800. This retains the literal max4 permutation action and actual PSL₂ matrices at every word transition. -/

@[expose] public section
open Theory.GroupTheory Subgroup
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4

def paired0 := wordSubgroup (fun i => (L0Gen i,target0Gen i)) L0Inv
  (fun i => Prod.ext (L0Inv_spec i) (target0Inv i))
def paired1 := wordSubgroup (fun i => (L1Gen i,target1Gen i)) L1Inv
  (fun i => Prod.ext (L1Inv_spec i) (target1Inv i))
def paired2 := wordSubgroup (fun i => (L2Gen i,target2Gen i)) L2Inv
  (fun i => Prod.ext (L2Inv_spec i) (target2Inv i))
def paired3 := wordSubgroup (fun i => (L3Gen i,target3Gen i)) L3Inv
  (fun i => Prod.ext (L3Inv_spec i) (target3Inv i))

theorem target0Step (i:Fin 4)(r:Fin 300) :
    target0Gen i*target0Rep r = target0Rep (L0Act i r)*evalWord target1Gen (L0Factor i r) :=
  projective_transition _ _ _ _ _ _ _ _ _ (raw0Step i r)
theorem target1Step (i:Fin 4)(r:Fin 13) :
    target1Gen i*target1Rep r = target1Rep (L1Act i r)*evalWord target2Gen (L1Factor i r) :=
  projective_transition _ _ _ _ _ _ _ _ _ (raw1Step i r)
theorem target2Step (i:Fin 2)(r:Fin 2) :
    target2Gen i*target2Rep r = target2Rep (L2Act i r)*evalWord target3Gen (L2Factor i r) := by
  have h := projective_transition _ _ _ (raw2Gen_det i) (raw2Rep_det r) (raw2Rep_det (L2Act i r)) raw3Gen raw3Gen_det _ (raw2Step i r)
  have he : (fun i:Fin 0 => pi ((raw3Gen i).sl (raw3Gen_det i)))=target3Gen :=
    funext (fun i => Fin.elim0 i)
  rw [he] at h
  exact h

theorem paired_card_bound : Nat.card paired0≤7800 := by
  have h0 := card_le_of_paired_transitions L0Gen target0Gen L0Inv L0Inv_spec target0Inv
    L1Gen target1Gen L1Inv L1Inv_spec target1Inv L0Rep target0Rep L0Act L0Factor 0
    L0Rep_initial target0Rep_initial L0step target0Step
  have h1 := card_le_of_paired_transitions L1Gen target1Gen L1Inv L1Inv_spec target1Inv
    L2Gen target2Gen L2Inv L2Inv_spec target2Inv L1Rep target1Rep L1Act L1Factor 0
    L1Rep_initial target1Rep_initial L1step target1Step
  have h2 := card_le_of_paired_transitions L2Gen target2Gen L2Inv L2Inv_spec target2Inv
    L3Gen target3Gen L3Inv L3Inv_spec target3Inv L2Rep target2Rep L2Act L2Factor 0
    L2Rep_initial target2Rep_initial L2step target2Step
  have h3 : Nat.card paired3=1 := by
    rw [paired3,wordSubgroup_fin_zero_eq_bot,Subgroup.card_bot]
  change Nat.card paired0≤300*Nat.card paired1 at h0
  change Nat.card paired1≤13*Nat.card paired2 at h1
  change Nat.card paired2≤2*Nat.card paired3 at h2
  rw [h3] at h2
  omega
end Tits.Max4Projective
