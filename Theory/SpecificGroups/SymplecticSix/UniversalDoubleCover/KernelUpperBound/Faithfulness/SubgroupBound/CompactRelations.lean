module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.ReplayData
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.SchreierLifting

/-!
# Compact Schreier relations and generation

Each of the 64 stored generator eliminations follows from one original raw
relation by previously proved substitutions, inversion, conjugation and free
cancellation. Strictly earlier dependency indices justify induction. Explicit
intermediate words prevent replay from recomputing its history.

The same checked operations prove all 51 compact relations. Checked expansions
express every one of the 72 raw edges in the eight retained edges, which then
generate the whole raw presentation. No finite order or model identity is used.

Source: ATLAS `S62G1-P1.M`, M2; the elimination trace is `source/schreier.json`.
See `source/README.md` and `source/generate_replay.py` for certificate provenance.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
open Subgroup.CosetWordCertificate CompactReplay

private abbrev rawImage (e : Edge) : RawPresentation := PresentedGroup.of e

private theorem rawImage_relator (r : RelatorIndex) : eval rawImage (rawRelator r) = 1 := by
  change FreeGroup.lift rawImage (FreeGroup.mk (rawRelator r)) = 1
  have he := FreeGroup.lift_unique (f := rawImage)
    (PresentedGroup.mk (Set.range (fun i => FreeGroup.mk (rawRelator i)))) (fun _ => rfl)
    (x := FreeGroup.mk (rawRelator r))
  exact he.symm.trans (PresentedGroup.one_of_mem ⟨r, rfl⟩)

private theorem certificate_valid (c : Certificate) (v : Word Edge)
    (h : ∀ s ∈ c.steps, rawImage (elimination s.1).1 = eval rawImage (elimination s.1).2)
    (hc : checkCertificate c v = true) : eval rawImage v = 1 := by
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq] at hc
  apply eval_conjugate_checked rawImage c.result v c.conjugator c.positive hc.2
  exact (eval_of_checkReplay rawImage elimination c.steps _ _ h hc.1).trans
    (rawImage_relator c.source)

private theorem elimination_acyclic : ∀ i : Fin 64,
    ∀ j ∈ (eliminationCertificate i).steps, j.1.val < i.val := by decide +kernel

set_option maxRecDepth 10000 in
private theorem elimination_checked : ∀ i : Fin 64,
    checkCertificate (eliminationCertificate i)
      ([((elimination i).1, true)] ++ FreeGroup.invRev (elimination i).2) = true := by decide +kernel

private theorem elimination_sound (i : Fin 64) :
    rawImage (elimination i).1 = eval rawImage (elimination i).2 := by
  have h : ∀ n (hn : n < 64), rawImage (elimination ⟨n, hn⟩).1 =
      eval rawImage (elimination ⟨n, hn⟩).2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      apply eq_of_eval_relation
      apply certificate_valid (eliminationCertificate ⟨n, hn⟩) _ ?_
        (elimination_checked ⟨n, hn⟩)
      intro j hj
      exact ih j.1.val (elimination_acyclic ⟨n, hn⟩ j hj) j.1.isLt
  exact h i.val i.isLt

set_option maxRecDepth 10000 in
private theorem relation_checked : ∀ i : Fin 51,
    checkCertificate (relationCertificate i)
      ((compactRelator i).map (fun a => (compactIndex a.1, a.2))) = true := by decide +kernel

/-- All 51 relations hold on the prescribed retained edges of the raw presentation. -/
theorem compactRelator_eval (r : Fin 51) : eval compactImage (compactRelator r) = 1 := by
  have h := certificate_valid (relationCertificate r) _
    (fun j _ => elimination_sound j.1) (relation_checked r)
  rw [eval_map_letters] at h
  exact h

set_option maxRecDepth 10000 in
private theorem expansion_checked : ∀ i : Fin 72,
    checkReplay elimination (expansionSteps i) [(numberedEdge i, true)]
      ((expansionWord i).map (fun a => (compactIndex a.1, a.2))) = true := by decide +kernel

private theorem expansion_sound (i : Fin 72) :
    rawImage (numberedEdge i) = eval compactImage (expansionWord i) := by
  have h := eval_of_checkReplay rawImage elimination (expansionSteps i)
    [(numberedEdge i, true)] _ (fun j _ => elimination_sound j.1) (expansion_checked i)
  rw [eval_map_letters, eval_letter] at h
  exact h.symm

private theorem numberedEdge_surjective : Function.Surjective numberedEdge := by
  decide +kernel

/-- The eight retained edges generate the entire raw presentation. -/
theorem compactImage_generates : Subgroup.closure (Set.range compactImage) = ⊤ := by
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by _ _ ?_ x
  intro e
  obtain ⟨i, rfl⟩ := numberedEdge_surjective e
  change rawImage (numberedEdge i) ∈ Subgroup.closure (Set.range compactImage)
  rw [expansion_sound]
  exact eval_mem_of_generators_mem _ compactImage
    (fun a => Subgroup.subset_closure (k := Set.range compactImage) ⟨a, rfl⟩) _

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
