module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.SchreierData
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!
# Unconditional lifting of the Schreier relations

The edge elements are literal words in the seven-relator ATLAS presentation.
Products along a path telescope. The finite endpoint and inverse checks thus
prove all 252 rewritten relations, while free cancellation proves the 35 tree
relations. The resulting homomorphism has image containing both M2 generators.
Consequently a finite bound on this auxiliary presentation bounds the actual
subgroup, without assuming either coset faithfulness or a matrix identification.

Source: ATLAS `S62G1-P1.M`, M2; extraction data are described in `source/README.md`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
open Subgroup.CosetWordCertificate

private theorem sourceWord_eval (r : Fin 7) : eval generator (sourceWord r) = 1 := by
  have h := relator_eval r
  fin_cases r <;>
    simpa [sourceWord, eval, FreeGroup.lift_mk, word, sourceCommutator,
      pow_succ, mul_assoc] using h

private theorem step_inverse : ∀ (i : Vertex) (a : Bool),
    step (step i (a, false)) (a, true) = i := by decide +kernel

private theorem source_loop : ∀ (i : Vertex) (r : Fin 7),
    endpoint i (sourceWord r) = i := by decide +kernel

private theorem tree_reduces : ∀ k : Fin 35, reduce (edgeWord (treeEdge k)) = [] :=
  by decide +kernel

def representative (i : Vertex) : Presented := eval generator (representativeWord i)
def edgeGenerator (e : Edge) : Presented := eval generator (edgeWord e)

private theorem edgeGenerator_eq (i : Vertex) (a : Bool) :
    edgeGenerator (i, a) = representative i * generator a *
      (representative (step i (a, true)))⁻¹ := by
  rw [edgeGenerator, edgeWord, eval_append, eval_append, eval_invRev]
  rfl

/-- Schreier rewriting is an equality of actual group elements. -/
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

/-- All defining relations of the auxiliary presentation hold in the original group. -/
theorem rawRelator_eval (r : RelatorIndex) : eval edgeGenerator (rawRelator r) = 1 := by
  rcases r with ⟨i, r⟩ | k
  · rw [rawRelator, eval_rewrite, source_loop, sourceWord_eval]
    simp
  · rw [rawRelator]
    rw [eval_letter]
    change edgeGenerator (treeEdge k) = 1
    rw [edgeGenerator, ← eval_reduce, tree_reduces]
    exact eval_nil _

/-- The homomorphism interprets every edge as its literal original word. -/
def realization : RawPresentation →* Presented :=
  PresentedGroup.toGroup (f := edgeGenerator)
    (by rintro _ ⟨r, rfl⟩; exact rawRelator_eval r)

theorem realization_of (e : Edge) : realization (PresentedGroup.of e) = edgeGenerator e :=
  PresentedGroup.toGroup.of _

private def markWord : Bool → Word Bool
  | false => [(false, true)]
  | true => [(true, true), (false, true), (true, true), (true, true), (true, true)]

private theorem mark_loop : ∀ a : Bool, endpoint 0 (markWord a) = 0 := by decide +kernel

private theorem mark_eval (a : Bool) :
    eval edgeGenerator (rewrite 0 (markWord a)) = s8Generator a := by
  rw [eval_rewrite, mark_loop]
  cases a <;> simp [representative, representativeWord, markWord, eval_cons,
    s8Generator, pow_succ, mul_assoc]

/-- Both literal M2 generators lie in the image; no subgroup identification is needed. -/
theorem s8Subgroup_le_range : s8Subgroup ≤ realization.range := by
  change Subgroup.closure (Set.range s8Generator) ≤ realization.range
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a, rfl⟩
  rw [← mark_eval a]
  apply eval_mem_of_generators_mem
  intro e
  exact ⟨PresentedGroup.of e, realization_of e⟩

/-- The required abstract-subgroup bound follows from a bound on the edge presentation. -/
theorem s8Subgroup_bound_of_raw_bound
    (h : Finite RawPresentation ∧ Nat.card RawPresentation ≤ 40320) :
    Finite s8Subgroup ∧ Nat.card s8Subgroup ≤ 40320 := by
  let : Finite RawPresentation := h.1
  let : Finite realization.range :=
    Finite.of_surjective _ realization.rangeRestrict_surjective
  let f := Subgroup.inclusion s8Subgroup_le_range
  have hf : Function.Injective f := Subgroup.inclusion_injective _
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans
      ((Nat.card_le_card_of_surjective _ realization.rangeRestrict_surjective).trans h.2)⟩

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
