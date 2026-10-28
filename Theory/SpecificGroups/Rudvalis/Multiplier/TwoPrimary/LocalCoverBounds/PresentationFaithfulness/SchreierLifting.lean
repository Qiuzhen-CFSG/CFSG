module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.TableChecks
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!+# A 168-representative bound for the original max4 presentation

The 336 edge generators are literal words in the original two generators.
The inverse table, the seven source loops at each vertex, and the 167 tree
edges are kernel checked. Telescoping therefore realizes the raw presentation
in the original presentation. Its image contains every transition difference,
so 168 representatives cover the original group modulo this image.

No order or identification of the table's permutation group is needed.
A finite bound of 2048 on the raw presentation gives the desired bound 344064.
Source: the original seven max4 words supporting Aschbacher--Smith I.1.3(1),
printed p.407; see `source/README.md` for discovery and certificate provenance.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
open Subgroup.CosetWordCertificate

private theorem sourceWord_eval (r : Fin 7) : eval generator (sourceWord r) = 1 := by
  have h := toPresented_relator r
  change toPresented (word (FreeGroup.of false) (FreeGroup.of true) r) = 1 at h
  rw [map_word] at h
  have h' : word (generator false) (generator true) r = 1 := by
    simpa only [generator, toPresented, PresentedGroup.of] using h
  fin_cases r <;>
    simpa [sourceWord, eval, FreeGroup.lift_mk, word, pow_succ, mul_assoc] using h'

private theorem step_inverse : ∀ (i : Vertex) (a : Bool),
    step (step i (a, false)) (a, true) = i := TableChecks.step_inverse

private theorem source_loop : ∀ (i : Vertex) (r : Fin 7),
    endpoint i (sourceWord r) = i := TableChecks.source_loop

private theorem tree_reduces : ∀ k : Fin 167, reduce (edgeWord (treeEdge k)) = [] :=
  TableChecks.tree_reduces

def representative (i : Vertex) : Presented := eval generator (representativeWord i)
def edgeGenerator (e : Edge) : Presented := eval generator (edgeWord e)

theorem edgeGenerator_eq (i : Vertex) (a : Bool) :
    edgeGenerator (i, a) = representative i * generator a *
      (representative (step i (a, true)))⁻¹ := by
  rw [edgeGenerator, edgeWord, eval_append, eval_append, eval_invRev]
  rfl

/-- Schreier rewriting telescopes in the literal seven-relator presentation. -/
theorem eval_rewrite (i : Vertex) (w : Word Bool) :
    eval edgeGenerator (rewrite i w) =
      representative i * eval generator w * (representative (endpoint i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [rewrite, endpoint]
  | cons a w ih =>
      rcases a with ⟨a, sign⟩
      cases sign
      · simp only [rewrite, Bool.false_eq_true, ↓reduceIte, eval_cons, ih, endpoint,
          edgeGenerator_eq, step_inverse, mul_inv_rev, inv_inv]
        simp [mul_assoc]
      · simp only [rewrite, ↓reduceIte, eval_cons, ih, endpoint, edgeGenerator_eq]
        simp [mul_assoc]

/-- All 1343 raw relations hold on the prescribed literal edge words. -/
theorem rawRelator_eval (r : RelatorIndex) : eval edgeGenerator (rawRelator r) = 1 := by
  rcases r with ⟨i, r⟩ | k
  · rw [rawRelator, eval_rewrite, source_loop, sourceWord_eval]
    simp
  · rw [rawRelator, eval_letter]
    change edgeGenerator (treeEdge k) = 1
    rw [edgeGenerator, ← eval_reduce, tree_reduces]
    exact eval_nil _

/-- Interpret every raw generator as its original two-generator word. -/
def realization : RawPresentation →* Presented :=
  PresentedGroup.toGroup (f := edgeGenerator)
    (by rintro _ ⟨r, rfl⟩; exact rawRelator_eval r)

theorem realization_of (e : Edge) : realization (PresentedGroup.of e) = edgeGenerator e :=
  PresentedGroup.toGroup.of _

private theorem edgeGenerator_mem (e : Edge) : edgeGenerator e ∈ realization.range :=
  ⟨PresentedGroup.of e, realization_of e⟩

/-- Each transition has an actual witness in the image of the raw presentation. -/
def cosetCover : Subgroup.GeneratorCosetCover realization.range generator Vertex where
  repr := representative
  initial := 0
  initial_eq := by simp [representative, representativeWord]
  step i a := by
    refine ⟨⟨edgeGenerator (i, a), edgeGenerator_mem _⟩, step i (a, true), ?_⟩
    change representative i * generator a = edgeGenerator (i, a) * _
    rw [edgeGenerator_eq, inv_mul_cancel_right]
  inv_step i a := by
    refine ⟨⟨(edgeGenerator (step i (a, false), a))⁻¹,
      realization.range.inv_mem (edgeGenerator_mem _)⟩, step i (a, false), ?_⟩
    change representative i * (generator a)⁻¹ =
      (edgeGenerator (step i (a, false), a))⁻¹ * _
    rw [edgeGenerator_eq, step_inverse]
    simp [mul_assoc]

/-- A bound on the edge presentation bounds the original seven-relator group. -/
theorem presented_bound_of_raw_bound
    (h : Finite RawPresentation ∧ Nat.card RawPresentation ≤ 2048) :
    Finite Presented ∧ Nat.card Presented ≤ 344064 := by
  let : Finite RawPresentation := h.1
  let : Finite realization.range :=
    Finite.of_surjective _ realization.rangeRestrict_surjective
  obtain ⟨hf, hb⟩ := cosetCover.finite_card_le
    (PresentedGroup.closure_range_of (Set.range relator))
  refine ⟨hf, hb.trans ?_⟩
  have hcard : Nat.card realization.range ≤ 2048 :=
    (Nat.card_le_card_of_surjective _ realization.rangeRestrict_surjective).trans h.2
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 168 hcard

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
