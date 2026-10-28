module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices
/-!
# Normalizing the inverting involution

With the cubic operator in permutation coordinates, the inversion relation
forces the second and third columns of an involution from its first column.
A kernel-checked two-column calculation constructs a basis commuting with
the cubic operator and conjugating the involution to the ordinary or the
parity-twisted transposition. The twelve surviving matrices are handled by
explicit invertible intertwiners. Thus the original actor labels are retained.

This is the elementary S₃ coordinate step supporting Huppert–Blackburn,
*Finite Groups III*, XII.1.18(b), p.314, not the final S₄ classification.
-/

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization

private def cubicSquare : Mat := (4,1,2,8)
private def reduced (a d : Code) : Mat := (a, app cubicSquare a, app cubic a, d)
private def invertingBasis (a d : Code) : Mat :=
  match a.val, d.val with
  | 1, 8 => (2,4,1,8)
  | 1, 15 => (10,12,9,8)
  | 2, 8 => (1,2,4,8)
  | 2, 15 => (9,10,12,8)
  | 4, 8 => (4,1,2,8)
  | 4, 15 => (11,14,13,15)
  | 9, 8 => (2,4,1,15)
  | 10, 8 => (1,2,4,15)
  | 11, 7 => (4,1,2,8)
  | 12, 8 => (4,1,2,15)
  | 13, 7 => (1,2,4,8)
  | 14, 7 => (2,4,1,8)
  | _, _ => ident

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem inverting_certificate : ∀ a d : Code,
    let m := reduced a d
    let f := invertingBasis a d
    comp m m = ident → comp m cubic = comp cubicSquare m →
    trivialKernel f ∧ comp cubic f = comp f cubic ∧
      (comp m f = comp f ordinary ∨ comp m f = comp f twisted) := by
  decide +kernel

private theorem reduced_of_inverting (m : Mat)
    (h : comp m cubic = comp cubicSquare m) : m = reduced m.1 m.2.2.2 := by
  have hb := congrArg (fun n : Mat => n.1) h
  change app m 2 = app cubicSquare m.1 at hb
  rw [show app m 2 = m.2.1 from app_basis m 1] at hb
  have hc := congrArg (fun n : Mat => n.2.1) h
  change app m 4 = app cubicSquare m.2.1 at hc
  rw [show app m 4 = m.2.2.1 from app_basis m 2, hb] at hc
  have hs : ∀ v : Code, app cubicSquare (app cubicSquare v) = app cubic v := by
    decide +kernel
  rw [hs] at hc
  exact Prod.ext rfl (Prod.ext hb (Prod.ext hc rfl))

private theorem lin_square : lin cubicSquare =
    ((permutationAction threeCycle) * (permutationAction threeCycle)).toMonoidHom := by
  have h : comp cubic cubic = cubicSquare := by decide +kernel
  rw [← h, lin_comp, lin_cubic]
  rfl

public theorem normalize_inverting (t : MulAut BinaryFour) (hsq : t * t = 1)
    (hinv : t * permutationAction threeCycle =
      (permutationAction threeCycle * permutationAction threeCycle) * t) :
    ∃ f : MulAut BinaryFour,
      (∀ v, permutationAction threeCycle (f v) = f (permutationAction threeCycle v)) ∧
      ((∀ v, t (f v) = f (permutationAction transposition v)) ∨
        (∀ v, t (f v) = f (twistedAction transposition v))) := by
  let m := ofAut t
  have hm : comp m m = ident := by
    rw [← ofAut_mul, hsq, ofAut_one]
  have hi : comp m cubic = comp cubicSquare m := by
    apply lin_injective
    rw [lin_comp, lin_comp, lin_ofAut, lin_cubic, lin_square]
    exact congrArg MulEquiv.toMonoidHom hinv
  have hr := reduced_of_inverting m hi
  have hcert := inverting_certificate m.1 m.2.2.2
  rw [← hr] at hcert
  obtain ⟨hf, hfc, hft⟩ := hcert hm hi
  refine ⟨aut _ hf, ?_, ?_⟩
  · have he := congrArg lin hfc
    rw [lin_comp, lin_comp, lin_cubic] at he
    intro v
    exact congrArg (fun h : BinaryFour →* BinaryFour => h v) he
  · rcases hft with hft | hft
    · left
      have he := congrArg lin hft
      rw [lin_comp, lin_comp, lin_ofAut, lin_ordinary] at he
      intro v
      exact congrArg (fun h : BinaryFour →* BinaryFour => h v) he
    · right
      have he := congrArg lin hft
      rw [lin_comp, lin_comp, lin_ofAut, lin_twisted] at he
      intro v
      exact congrArg (fun h : BinaryFour →* BinaryFour => h v) he
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
