module
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Conjugating an involution in a fixed-free binary A4 action

For the displayed fixed-free cubic on the four-dimensional binary module,
an involution satisfying the A4 conjugate relations has a change of basis
which preserves that cubic and sends the involution to the displayed shear.
The conclusion concerns the supplied automorphisms; the finite encoding is
private and creates no alternative action instance.

The proof encodes linear maps by their four images of a binary basis. Kernel
computation checks the 16 possible first columns separately, finding exactly
15 involutions. For each candidate an explicit matrix and inverse give the
required change of basis, again checked in the kernel. Injectivity of the
encoding then transports these identities back to actual automorphisms.
This finite representation lemma supports the normalizer obstruction in
Stellmacher's (8.6)(b), replacing the unsupported action-image identification
in the printed p.44 argument with an explicit A4 calculation.
-/

namespace FixedFreeA4InvolutionConjugacy
private abbrev B := Fin 16
private abbrev Code := B × B × B × B
private def xor (a b : B) : B := (BitVec.ofFin (w := 4) a ^^^ BitVec.ofFin (w := 4) b).toFin
private def applyCode (c : Code) (v : B) : B :=
  xor (xor (xor (if v.val.testBit 0 then c.1 else 0)
    (if v.val.testBit 1 then c.2.1 else 0))
    (if v.val.testBit 2 then c.2.2.1 else 0))
    (if v.val.testBit 3 then c.2.2.2 else 0)
private def mulCode (a b : Code) : Code :=
  (applyCode a b.1,applyCode a b.2.1,applyCode a b.2.2.1,applyCode a b.2.2.2)
private def identity : Code := (1,2,4,8)
private def reflection : Code := (1,2,5,10)
private def cubic : Code := (2,3,12,4)
private def cubicInv : Code := (3,1,8,12)
private abbrev V := Fin 4 → Multiplicative (ZMod 2)
private abbrev Aut := MulAut V
private def vector (b : B) : V := fun i =>
  Multiplicative.ofAdd (if b.val.testBit i.val then 1 else 0)
private def unvector (v : V) : B :=
  ((List.finRange 16).find? (fun b => vector b = v)).getD 0
private theorem vector_unvector : ∀ v : V, vector (unvector v) = v := by decide +kernel
private theorem unvector_vector : ∀ b : B, unvector (vector b) = b := by decide +kernel
private theorem vector_injective : Function.Injective vector :=
  Function.LeftInverse.injective unvector_vector
private theorem vector_surjective : Function.Surjective vector :=
  Function.RightInverse.surjective vector_unvector
private theorem vector_zero : vector 0 = 1 := by decide +kernel
private theorem vector_xor : ∀ a b : B, vector (xor a b) = vector a * vector b := by
  decide +kernel
private theorem vector_decomposition : ∀ b : B,
    vector b = (if b.val.testBit 0 then vector 1 else 1) *
      (if b.val.testBit 1 then vector 2 else 1) *
      (if b.val.testBit 2 then vector 4 else 1) *
      (if b.val.testBit 3 then vector 8 else 1) := by decide +kernel
private def code (f : Aut) : Code :=
  (unvector (f (vector 1)),unvector (f (vector 2)),
    unvector (f (vector 4)),unvector (f (vector 8)))
private theorem apply_code (f : Aut) (b : B) :
    vector (applyCode (code f) b) = f (vector b) := by
  rw [vector_decomposition b,map_mul,map_mul,map_mul]
  simp only [applyCode,code,vector_xor]
  split_ifs <;> simp only [map_one,vector_zero,vector_unvector]
private theorem code_mul (f g : Aut) : code (f*g) = mulCode (code f) (code g) := by
  have hc (b : B) : vector (unvector ((f*g) (vector b))) =
      vector (applyCode (code f) (unvector (g (vector b)))) := by
    rw [apply_code,vector_unvector,vector_unvector]
    rfl
  exact Prod.ext (vector_injective (hc 1))
    (Prod.ext (vector_injective (hc 2))
      (Prod.ext (vector_injective (hc 4)) (vector_injective (hc 8))))
private theorem code_injective : Function.Injective (fun f : Aut => code f) := by
  intro f g h
  apply MulEquiv.ext
  intro v
  obtain ⟨b,rfl⟩ := vector_surjective v
  rw [←apply_code f,←apply_code g]
  exact congrArg (fun c => vector (applyCode c b)) h
private def reflectionAut : Aut where
  toFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  invFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private def cubicAut : Aut where
  toFun v := ![v 1,v 0*v 1,v 2*v 3,v 2]
  invFun v := ![v 0*v 1,v 0,v 3,v 2*v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private theorem code_reflection : code reflectionAut = reflection := by decide +kernel
private theorem code_cubic : code cubicAut = cubic := by decide +kernel
private theorem code_cubic_inverse : code (cubicAut⁻¹) = cubicInv := by decide +kernel

private def reflections : Fin 15 → Code := ![
  (1,2,5,10),
  (1,2,6,11),
  (1,2,7,9),
  (4,9,1,6),
  (5,10,4,8),
  (6,8,9,2),
  (7,11,13,14),
  (8,13,11,1),
  (9,14,4,8),
  (10,12,15,13),
  (11,15,3,5),
  (12,5,14,15),
  (13,6,4,8),
  (14,4,2,7),
  (15,7,10,3)]

private def frames : Fin 15 → Code := ![
  (1,2,4,8),
  (1,2,8,12),
  (1,2,12,4),
  (4,12,5,11),
  (4,12,1,3),
  (4,12,9,15),
  (4,12,13,7),
  (4,12,14,5),
  (4,12,2,1),
  (4,12,6,9),
  (4,12,10,13),
  (4,12,11,14),
  (4,12,3,2),
  (4,12,15,6),
  (4,12,7,10)]

private def inverseFrames : Fin 15 → Code := ![
  (1,2,4,8),
  (1,2,12,4),
  (1,2,8,12),
  (5,14,1,3),
  (4,12,1,3),
  (7,13,1,3),
  (6,15,1,3),
  (9,6,1,3),
  (8,4,1,3),
  (11,5,1,3),
  (10,7,1,3),
  (13,10,1,3),
  (12,8,1,3),
  (15,9,1,3),
  (14,11,1,3)]

private def related (r : Code) : Prop :=
  let s := mulCode (mulCode cubic r) cubicInv
  let q := mulCode (mulCode cubicInv r) cubic
  r ≠ identity ∧ mulCode r r = identity ∧ mulCode r s = mulCode s r ∧
    mulCode (mulCode r s) q = identity
private instance (r : Code) : Decidable (related r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_0 : ∀ b c d : B, related (0,b,c,d) →
    ∃ k : Fin 15, (0,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_1 : ∀ b c d : B, related (1,b,c,d) →
    ∃ k : Fin 15, (1,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_2 : ∀ b c d : B, related (2,b,c,d) →
    ∃ k : Fin 15, (2,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_3 : ∀ b c d : B, related (3,b,c,d) →
    ∃ k : Fin 15, (3,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_4 : ∀ b c d : B, related (4,b,c,d) →
    ∃ k : Fin 15, (4,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_5 : ∀ b c d : B, related (5,b,c,d) →
    ∃ k : Fin 15, (5,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_6 : ∀ b c d : B, related (6,b,c,d) →
    ∃ k : Fin 15, (6,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_7 : ∀ b c d : B, related (7,b,c,d) →
    ∃ k : Fin 15, (7,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_8 : ∀ b c d : B, related (8,b,c,d) →
    ∃ k : Fin 15, (8,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_9 : ∀ b c d : B, related (9,b,c,d) →
    ∃ k : Fin 15, (9,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_10 : ∀ b c d : B, related (10,b,c,d) →
    ∃ k : Fin 15, (10,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_11 : ∀ b c d : B, related (11,b,c,d) →
    ∃ k : Fin 15, (11,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_12 : ∀ b c d : B, related (12,b,c,d) →
    ∃ k : Fin 15, (12,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_13 : ∀ b c d : B, related (13,b,c,d) →
    ∃ k : Fin 15, (13,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_14 : ∀ b c d : B, related (14,b,c,d) →
    ∃ k : Fin 15, (14,b,c,d) = reflections k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem classify_15 : ∀ b c d : B, related (15,b,c,d) →
    ∃ k : Fin 15, (15,b,c,d) = reflections k := by
  decide +kernel

private theorem classify (r : Code) (hr : related r) : ∃ k : Fin 15, r = reflections k := by
  obtain ⟨a,b,c,d⟩ := r
  fin_cases a
  · exact classify_0 b c d hr
  · exact classify_1 b c d hr
  · exact classify_2 b c d hr
  · exact classify_3 b c d hr
  · exact classify_4 b c d hr
  · exact classify_5 b c d hr
  · exact classify_6 b c d hr
  · exact classify_7 b c d hr
  · exact classify_8 b c d hr
  · exact classify_9 b c d hr
  · exact classify_10 b c d hr
  · exact classify_11 b c d hr
  · exact classify_12 b c d hr
  · exact classify_13 b c d hr
  · exact classify_14 b c d hr
  · exact classify_15 b c d hr

private theorem frame_left : ∀ (k : Fin 15) (v : V),
    vector (applyCode (inverseFrames k)
      (unvector (vector (applyCode (frames k) (unvector v))))) = v := by
  decide +kernel
private theorem frame_right : ∀ (k : Fin 15) (v : V),
    vector (applyCode (frames k)
      (unvector (vector (applyCode (inverseFrames k) (unvector v))))) = v := by
  decide +kernel
private theorem frame_mul : ∀ (k : Fin 15) (v w : V),
    vector (applyCode (frames k) (unvector (v*w))) =
      vector (applyCode (frames k) (unvector v)) *
        vector (applyCode (frames k) (unvector w)) := by
  decide +kernel
private def frameAut (k : Fin 15) : Aut where
  toFun v := vector (applyCode (frames k) (unvector v))
  invFun v := vector (applyCode (inverseFrames k) (unvector v))
  left_inv := frame_left k
  right_inv := frame_right k
  map_mul' := frame_mul k
private theorem code_frame : ∀ k : Fin 15, code (frameAut k) = frames k := by
  decide +kernel
private theorem code_frame_inverse : ∀ k : Fin 15,
    code ((frameAut k)⁻¹) = inverseFrames k := by
  decide +kernel
private theorem frames_fix_cubic : ∀ k : Fin 15,
    mulCode (mulCode (frames k) cubic) (inverseFrames k) = cubic := by
  decide +kernel
private theorem frames_normalize_reflection : ∀ k : Fin 15,
    mulCode (mulCode (frames k) (reflections k)) (inverseFrames k) = reflection := by
  decide +kernel
private theorem code_one : code (1 : Aut) = identity := by decide +kernel
private theorem code_cubic_square : code (cubicAut^2) = cubicInv := by decide +kernel
private theorem code_cubic_square_inverse : code ((cubicAut^2)⁻¹) = cubic := by
  decide +kernel

end FixedFreeA4InvolutionConjugacy
open FixedFreeA4InvolutionConjugacy

public theorem MulAut.exists_conjugacy_fixed_free_a4_involution
    (r t : MulAut (Fin 4 → Multiplicative (ZMod 2)))
    (ht : ∀ v, t v = ![v 1, v 0*v 1, v 2*v 3, v 2])
    (hrne : r ≠ 1) (hr2 : r^2 = 1)
    (hcomm : Commute r (t*r*t⁻¹))
    (hnorm : r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹) = 1) :
    ∃ a : MulAut (Fin 4 → Multiplicative (ZMod 2)),
      a*t*a⁻¹ = t ∧ ∀ v, (a*r*a⁻¹) v = ![v 0*v 2, v 1*v 3, v 2, v 3] := by
  have ht' : t = cubicAut := MulEquiv.ext ht
  subst t
  have hne : code r ≠ identity := by
    intro h
    exact hrne (code_injective (h.trans code_one.symm))
  have hsquare : mulCode (code r) (code r) = identity := by
    have h := congrArg code hr2
    simpa only [pow_two,code_mul,code_one] using h
  have hc : mulCode (code r) (mulCode (mulCode cubic (code r)) cubicInv) =
      mulCode (mulCode (mulCode cubic (code r)) cubicInv) (code r) := by
    have h := congrArg code hcomm.eq
    simpa only [code_mul,code_cubic,code_cubic_inverse] using h
  have hn : mulCode (mulCode (code r) (mulCode (mulCode cubic (code r)) cubicInv))
      (mulCode (mulCode cubicInv (code r)) cubic) = identity := by
    have h := congrArg code hnorm
    simpa only [code_mul,code_cubic,code_cubic_inverse,code_cubic_square,
      code_cubic_square_inverse,code_one] using h
  obtain ⟨k,hk⟩ := classify (code r) ⟨hne,hsquare,hc,hn⟩
  refine ⟨frameAut k,?_,?_⟩
  · apply code_injective
    simpa only [code_mul,code_frame,code_frame_inverse,code_cubic] using frames_fix_cubic k
  · have heq : frameAut k * r * (frameAut k)⁻¹ = reflectionAut := by
      apply code_injective
      simpa only [code_mul,code_frame,code_frame_inverse,code_reflection,hk]
        using frames_normalize_reflection k
    intro v
    rw [heq]
    rfl
