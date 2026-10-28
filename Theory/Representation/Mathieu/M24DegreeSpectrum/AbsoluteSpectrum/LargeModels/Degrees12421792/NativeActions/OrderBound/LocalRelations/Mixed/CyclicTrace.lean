module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Trace.Context
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Trace.Checked
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Trace.Output

/-!
# Realizing the mixed-word trace in the original source group

The only subgroup loop is `xyxyxy⁻¹`. All other loops are rotations or inverses
of the first four local relations and the definition of that extra letter.
Thus the quartic and first mixed relations suffice for cyclic membership of
all six fixed words. This statement does not assume their triviality, or an
order bound for the ambient presentation. See `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed.Trace
open Subgroup.CosetWordCertificate

def certificateGenerator (n : ℕ) : UniversalGroup :=
  if n = 0 then boundGenerator 0 else
  if n = 1 then boundGenerator 1 else cycleElement

@[simp] theorem certificateGenerator_fin (i : Fin 2) :
    certificateGenerator i.val = boundGenerator i := by
  fin_cases i <;> rfl

private theorem eval_map_letters (w : Word (Fin 2)) :
    eval certificateGenerator (w.map fun a => (a.1.val, a.2)) = eval boundGenerator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, eval_cons, certificateGenerator_fin, ih]

private def traceOriginal : Fin 5 → Word Nat :=
  ![(localRelatorLetters 0).map (fun a => (a.1.val, a.2)),
    (localRelatorLetters 1).map (fun a => (a.1.val, a.2)),
    (localRelatorLetters 2).map (fun a => (a.1.val, a.2)),
    (localRelatorLetters 3).map (fun a => (a.1.val, a.2)),
    cycleLetters.map (fun a => (a.1.val, a.2)) ++ [(2, false)]]

private theorem originals_exact : ∀ i : Fin 5, originals i = traceOriginal i := by
  decide +kernel

private theorem original_eval (hq : QuarticRelation) (hf : FirstRelation) (i : Fin 5) :
    eval certificateGenerator (originals i) = 1 := by
  rw [originals_exact]
  fin_cases i
  · change eval certificateGenerator ((localRelatorLetters 0).map _) = 1
    rw [eval_map_letters]
    exact localRelator_zero_holds
  · change eval certificateGenerator ((localRelatorLetters 1).map _) = 1
    rw [eval_map_letters]
    exact localRelator_one_holds
  · change eval certificateGenerator ((localRelatorLetters 2).map _) = 1
    rw [eval_map_letters]
    exact hq
  · change eval certificateGenerator ((localRelatorLetters 3).map _) = 1
    rw [eval_map_letters]
    exact hf
  · change eval certificateGenerator (cycleLetters.map _ ++ [(2, false)]) = 1
    rw [eval_append, eval_map_letters, eval_letter]
    change cycleElement * cycleElement⁻¹ = 1
    exact mul_inv_cancel _

private def variant (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  (if inv then FreeGroup.invRev w else w).rotate offset

private theorem eval_variant (w : Word Nat) (hw : eval certificateGenerator w = 1)
    (inv : Bool) (offset : Nat) : eval certificateGenerator (variant w inv offset) = 1 := by
  have h : eval certificateGenerator (if inv then FreeGroup.invRev w else w) = 1 := by
    cases inv <;> simp [hw, eval_invRev]
  simpa [eval, FreeGroup.lift_mk, variant, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one (by simpa [eval, FreeGroup.lift_mk] using h) offset

set_option maxRecDepth 10000 in
private theorem variants_exact : ∀ i : Fin 92,
    relatorTable i.val = variant (originals (variantTable i.val).1)
      (variantTable i.val).2.1 (variantTable i.val).2.2 := by decide +kernel

private theorem relator_ok (hq : QuarticRelation) (hf : FirstRelation) (r : Nat) :
    eval certificateGenerator (relatorWords r) = 1 := by
  let i : Fin 92 := ⟨min r 91, by omega⟩
  rw [relatorWords, variants_exact i]
  exact eval_variant _ (original_eval hq hf _) _ _

/-- The trace context is sound using only the first four local identities. -/
theorem certificate_valid (hq : QuarticRelation) (hf : FirstRelation) :
    Valid context (Subgroup.zpowers cycleElement) certificateGenerator
      (definitions.repr certificateGenerator) := by
  apply definitions.valid
  · intro a ha
    have he : a = (2, true) := beq_iff_eq.mp ha
    subst a
    simp [certificateGenerator]
  · exact relator_ok hq hf

private theorem output_shape : ∀ i : Fin 6,
    facts (output i) = ⟨0,
      (localRelatorLetters ⟨i.val + 3, by omega⟩).map (fun a => (a.1.val, a.2)), 0⟩ := by
  decide +kernel

/-- Every literal mixed word belongs to the cyclic subgroup used in the trace. -/
theorem mixed_mem_cycle (hq : QuarticRelation) (hf : FirstRelation) (i : Fin 6) :
    eval boundGenerator (localRelatorLetters ⟨i.val + 3, by omega⟩) ∈
      Subgroup.zpowers cycleElement := by
  have hh := all_hold (certificate_valid hq hf) (output i) (output_lt i)
  rw [output_shape] at hh
  obtain ⟨k, hk⟩ := hh
  change definitions.repr certificateGenerator 0 * eval certificateGenerator _ =
    k.val * definitions.repr certificateGenerator 0 at hk
  rw [Definitions.repr_zero, one_mul, mul_one, eval_map_letters] at hk
  exact hk.symm ▸ k.property

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed.Trace
