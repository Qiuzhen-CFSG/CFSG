module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# Twenty-one right cosets covering the exact max4 subgroup

Each of the published local words, multiplied on the right by any signed
max4 generator, is a candidate normal form times another published word.
The 84 equations are checked on the five-point base of the actual model.
Induction on words then proves coverage of max4, without an order bound.

`Local/source/Generate.py` reproduces the untrusted normal-form witnesses.
Lean checks their action equations against the preserved degree-4060 maps.
Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. ATLAS attribution and multiplication convention
are retained in `Representatives.WordLanguage` and `Sylow.Candidate`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
open Representatives RadicalCoverage.SylowCertificate

private def transitionData : Fin 21 → Fin 4 → Fin 21 × Fin 16384 :=
  ![![(1, 0), (2, 0), (1, 0), (3, 0)],
    ![(0, 0), (4, 0), (0, 0), (5, 0)],
    ![(2, 4428), (3, 0), (2, 4428), (0, 0)],
    ![(6, 0), (0, 0), (6, 0), (2, 0)],
    ![(4, 829), (5, 0), (4, 829), (1, 0)],
    ![(7, 0), (1, 0), (7, 0), (4, 0)],
    ![(3, 0), (8, 0), (3, 0), (9, 0)],
    ![(5, 0), (10, 0), (5, 0), (11, 0)],
    ![(12, 0), (9, 0), (12, 0), (6, 0)],
    ![(9, 72), (6, 0), (9, 72), (8, 0)],
    ![(13, 0), (11, 0), (13, 0), (7, 0)],
    ![(14, 0), (7, 0), (14, 0), (10, 0)],
    ![(8, 0), (15, 0), (8, 0), (13, 14431)],
    ![(10, 0), (12, 11319), (10, 0), (15, 11319)],
    ![(11, 0), (16, 0), (11, 0), (17, 0)],
    ![(17, 6952), (13, 14431), (17, 6952), (12, 0)],
    ![(18, 0), (17, 0), (18, 0), (14, 0)],
    ![(15, 5224), (14, 0), (15, 5224), (16, 0)],
    ![(16, 0), (19, 0), (16, 0), (20, 0)],
    ![(19, 13192), (20, 0), (19, 13192), (18, 0)],
    ![(20, 829), (18, 0), (20, 829), (19, 0)]]

set_option maxRecDepth 10000 in
private theorem transitionMaps :
    ∀ (i : Fin 21) (j : Fin 4) (x : Fin 5),
      localMap (localWords i) (LocalOrder.letterMap j (x.castLE (by decide))) =
        LocalOrder.normalMap (transitionData i j).2
          (localMap (localWords (transitionData i j).1) (x.castLE (by decide))) := by
  apply Rudvalis.OrderCertificate.allFin₃
  decide +kernel

private theorem transition (i : Fin 21) (j : Fin 4) :
    localValue (localWords i) * candidateLetter j =
      candidateNormalForm (transitionData i j).2 * localValue (localWords (transitionData i j).1) := by
  apply eq_of_smul_first_five
  intro x
  simp only [mul_smul, localValue_smul, LocalOrder.letter_smul, LocalOrder.normal_smul]
  exact transitionMaps i j x

private theorem local_cover_of_transitions
    (transition : ∀ (i : Fin 21) (j : Fin 4), ∃ (k : Fin 21) (n : Fin 16384),
      localValue (localWords i) * candidateLetter j =
        candidateNormalForm n * localValue (localWords k))
    {x : Model} (hx : x ∈ max4) :
    ∃ i p, p ∈ candidate ∧ x = p * localValue (localWords i) := by
  have step (z : Model)
      (hz : ∃ i p, p ∈ candidate ∧ z = p * localValue (localWords i))
      (j : Fin 4) :
      ∃ i p, p ∈ candidate ∧ z * candidateLetter j = p * localValue (localWords i) := by
    obtain ⟨i, p, hp, rfl⟩ := hz
    obtain ⟨k, n, hn⟩ := transition i j
    refine ⟨k, p * candidateNormalForm n, candidate.mul_mem hp (candidateNormalForm_mem n), ?_⟩
    rw [mul_assoc, hn, ← mul_assoc]
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, 1, candidate.one_mem, by rfl⟩
  | mul_right z _ y hy ih =>
    rcases hy with rfl | hy
    · exact step z ih 0
    · obtain rfl := Set.mem_singleton_iff.mp hy
      exact step z ih 1
  | mul_inv_cancel z _ y hy ih =>
    rcases hy with rfl | hy
    · exact step z ih 2
    · obtain rfl := Set.mem_singleton_iff.mp hy
      exact step z ih 3

/-- Every element of max4 is a candidate element times a published local word. -/
public theorem exists_local_factor {x : Model} (hx : x ∈ max4) :
    ∃ i p, p ∈ candidate ∧ x = p * localValue (localWords i) := by
  apply local_cover_of_transitions (fun i j =>
    ⟨(transitionData i j).1, (transitionData i j).2, transition i j⟩) hx

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
