module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Checks
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base

/-!
# Recovery words for candidate-derived overgroups

Each of the four noncandidate representatives for max1 and max2 recovers both
standard generators from the three commutator words and the representative.
Separately, two words recover the max4 generators from its commutator words,
proving that the literal max4 is perfect as an ambient subgroup.

The equalities are checked at the certified three-point base, with packed
permutations. All words are witnesses: GAP supplies no trusted result.
Source: the primary ATLAS programs and attribution in `MinimumIndex/source/`;
reproducible discovery is documented in `CandidateRigidity/source/`.
-/

namespace Tits.MinimumIndexThirteen.CandidateRigidity
open Theory.GroupTheory Subgroup Atlas1600OrderCertificate
open ConverseLocalCoverage.DoubleCosetCertificate WordChecks
set_option Elab.async false

private theorem recovery_checked (i : Fin 2) (j : Fin 4) (k : Fin 2) :
    evalWord (inputs (candidatePair (i.castLE (by decide)))
      (representative i ⟨j.val + 2, by omega⟩)) (recoveryWord i j k) =
      standard (k.castLE (by decide)) := by
  have hp (p : Fin 3) :
      (evalWord (inputs (candidatePair (i.castLE (by decide)))
        (representative i ⟨j.val + 2, by omega⟩)) (recoveryWord i j k)).val
        (p.castLE (by decide)) =
      (standard (k.castLE (by decide))).val (p.castLE (by decide)) := by
    rw [packed_eval, ← packed_representative, ← packed_standard]
    exact recovery_table i j k p
  exact threePoint_ext (hp 0) (hp 1) (hp 2)

private theorem eq_top_of_standard_mem (L : Subgroup Atlas1600Group)
    (ha : standard 0 ∈ L) (hb : standard 1 ∈ L) : L = ⊤ := by
  have hle : atlas1600Subgroup ≤ L.map inclusion := by
    apply (closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨standard 0, ha, rfl⟩
    · have hg' : g = atlas1600B := hg
      subst g
      exact ⟨standard 1, hb, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

/-- Every representative outside the corresponding candidate generates the
whole actual Atlas group together with that candidate's derived subgroup. -/
public theorem representative_generates (i : Fin 2) (j : Fin 6) (hj : 2 ≤ j.val) :
    candidateDerived (i.castLE (by decide)) ⊔ closure {representative i j} = ⊤ := by
  let k : Fin 4 := ⟨j.val - 2, by omega⟩
  have hk : (⟨k.val + 2, by omega⟩ : Fin 6) = j := by
    apply Fin.ext
    dsimp [k]
    omega
  have h (s : Fin 2) : standard (s.castLE (by decide)) ∈
      candidateDerived (i.castLE (by decide)) ⊔ closure {representative i j} := by
    have hm := eval_inputs_mem (i.castLE (by decide))
      (representative i ⟨k.val + 2, by omega⟩)
      (candidateDerived (i.castLE (by decide)) ⊔ closure {representative i j})
      le_sup_left (by rw [hk]; exact mem_sup_right (subset_closure (by simp)))
      (recoveryWord i k s)
    rw [recovery_checked] at hm
    exact hm
  exact eq_top_of_standard_mem _ (h 0) (h 1)

private theorem perfect_checked (k : Fin 2) :
    evalWord (inputs (candidatePair 2) 1) (perfectWord k) =
      ![(candidatePair 2).1, (candidatePair 2).2] k := by
  have hv (s : Fin 2) :
      (![(candidatePair 2).1, (candidatePair 2).2] s).val =
      ![(program L0G0 L0G1 2).1, (program L0G0 L0G1 2).2] s := by
    rw [packed_pair]
    fin_cases s <;> rfl
  have hp (p : Fin 3) :
      (evalWord (inputs (candidatePair 2) 1) (perfectWord k)).val
        (p.castLE (by decide)) =
      (![(candidatePair 2).1, (candidatePair 2).2] k).val
        (p.castLE (by decide)) := by
    rw [packed_eval, hv]
    exact perfect_table k p
  exact threePoint_ext (hp 0) (hp 1) (hp 2)

/-- The literal max4 candidate equals its ambient derived subgroup. -/
public theorem candidateDerived_two_eq : candidateDerived 2 = candidate 2 := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  rw [candidate_eq_closure]
  apply (closure_le _).mpr
  have h (k : Fin 2) : ![(candidatePair 2).1, (candidatePair 2).2] k ∈ candidateDerived 2 := by
    rw [← perfect_checked]
    exact eval_inputs_mem 2 1 _ le_rfl (Subgroup.one_mem _) (perfectWord k)
  intro x hx
  rcases hx with rfl | hx
  · exact h 0
  · have hx' : x = (candidatePair 2).2 := hx
    subst x
    exact h 1

end Tits.MinimumIndexThirteen.CandidateRigidity
