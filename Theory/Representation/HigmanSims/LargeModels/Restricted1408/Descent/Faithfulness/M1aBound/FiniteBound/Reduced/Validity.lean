module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Validity.Checked

/-!
# Literal validity of the marked ten-generator HS reduction

Every candidate relator is a consequence of the original 1,300 Schreier
relations. A checked sequence of cyclic rotations, multiplications by established
relations, and free cancellations proves these consequences in the abstract
101-generator carrier. The same certificate proves the three specified markings.
Consequently the existing presentation homomorphism is surjective, using the
already proved generation by original indices 0, 1 and 2.

Source: ATLAS HSG1-P1.M, via the literal Schreier presentation; see
`Validity/source/README.md`. No permutation-image calculation or finite upper
bound for either presentation is used here.
-/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
open Subgroup.CosetWordCertificate
open ValidityCertificate

/-- All 597 fixed candidate words hold in the original abstract carrier. -/
theorem candidate_relator_valid (r : Fin 597) :
    eval candidateGenerator (relatorWord r) = 1 := by
  change eval (fun x => localGenerator (originalIndex x)) (relatorWord r) = 1
  have hc := relator_checks r.val r.isLt
  simp only [relatorCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h := all_valid (relatorOutput r.val) hc.1
  rw [← hc.2] at h
  have he := (normalize_one_iff natGenerator _ _).mp h
  simpa only [reducedRaw, eval_toNatWord, Nat.mod_eq_of_lt r.isLt, eval_map_letters,
    candidateGenerator, Function.comp_def] using he

/-- The prescribed marking has the literal original indices 0, 1 and 2. -/
theorem candidate_marked_valid (i : Fin 3) :
    eval candidateGenerator (markedWord i) = Schreier.threeGenerator i := by
  change eval (fun x => localGenerator (originalIndex x)) (markedWord i) =
    Schreier.threeGenerator i
  have hc := marked_checks i.val i.isLt
  simp only [markedCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h := all_valid (markedOutput i.val) hc.1
  rw [← hc.2] at h
  have he := (normalize_one_iff natGenerator _ _).mp h
  have hi : i.val < 101 := by omega
  have hx := eq_of_eval_relation localGenerator ⟨i.val, hi⟩
    ((markedWord i).map (fun a => (originalIndex a.1, a.2)))
    (by simpa only [markedRaw, eval_toNatWord, Nat.mod_eq_of_lt i.isLt] using he)
  simpa only [eval_map_letters, candidateGenerator, Function.comp_def, threeGenerator]
    using hx.symm

/-- Actual application of both validity contracts to the existing transfer map. -/
theorem candidate_toOriginal_surjective :
    Function.Surjective (toOriginal candidate_relator_valid) :=
  toOriginal_surjective candidate_relator_valid candidate_marked_valid

/-- Only the independent finite bound remains for the original carrier. -/
theorem original_finite_card_of_reduced_bound
    (hb : Finite Carrier ∧ Nat.card Carrier ≤ 443520) :
    Finite Schreier.Carrier ∧ Nat.card Schreier.Carrier ≤ 443520 :=
  original_finite_card_of_inputs candidate_relator_valid candidate_marked_valid hb

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
