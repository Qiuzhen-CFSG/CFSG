module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration.Certificates.Data

/-!
# Kernel checks for HS five-conjugate generation

For each marked representative, the two recovery words are evaluated on all
100 points. Packed versions of the published generators avoid repeated
reduction of their original cycle expressions; their equality with those
original generators was already proved in `HS.OrderBound.Base`.

Source: the exact ATLAS HSG1-p100B0 action and GM02 Proposition 5.1.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration.Certificates
open Theory.GroupTheory _root_.Sporadic.LeechRelated.HS
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Certificate

private def generatorCheck : Bool :=
  checkFin (fun r : Fin 4 => checkFin (fun i : Fin 5 => checkFin (fun p : Fin 100 =>
    decide (generator r i p = generatorValue r i p))))

set_option maxRecDepth 10000 in
private theorem generator_checked : generatorCheck = true := by
  decide +kernel

private theorem generator_value (r : Fin 4) (i : Fin 5) (p : Fin 100) :
    generator r i p = generatorValue r i p :=
  of_decide_eq_true (checkedAt (checkedAt (checkedAt generator_checked r) i) p)

private theorem word_value (r : Fin 4) (w : List (Fin 5)) (p : Fin 100) :
    evalWord (generator r) w p = wordValue r w p := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change generator r i (evalWord (generator r) w p) =
      generatorValue r i (wordValue r w p)
    rw [ih, generator_value]

private def recoveryCheck (r : Fin 4) : Bool :=
  checkFin (fun p : Fin 100 => decide
    (wordValue r (recoveryA r) p = OrderCertificate.p0 p)) &&
  checkFin (fun p : Fin 100 => decide
    (wordValue r (recoveryB r) p = OrderCertificate.p1 p))

set_option maxRecDepth 10000 in
private theorem recovery_checked : ∀ r : Fin 4, recoveryCheck r = true := by
  apply allFin
  decide +kernel

/-- The first original carrier generator is recovered from five conjugates. -/
theorem recover_generatorA (r : Fin 4) :
    evalWord (generator r) (recoveryA r) = generatorA := by
  have h := (Bool.and_eq_true_iff.mp (recovery_checked r)).1
  apply Eq.trans _ OrderCertificate.a_eq_generator
  exact Equiv.ext (fun p => (word_value r _ p).trans (allFin _ h p))

/-- The second original carrier generator is recovered from five conjugates. -/
theorem recover_generatorB (r : Fin 4) :
    evalWord (generator r) (recoveryB r) = generatorB := by
  have h := (Bool.and_eq_true_iff.mp (recovery_checked r)).2
  apply Eq.trans _ OrderCertificate.b_eq_generator
  exact Equiv.ext (fun p => (word_value r _ p).trans (allFin _ h p))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration.Certificates
