module
public import Theory.GroupAction.BinaryA4Pair.Canonical
public import Theory.GroupAction.BinaryA4Pair.Data

/-!
# Normalizing a marked pair of binary A₄ actions

The first A₄ has its fixed-free cubic and shared involution in the displayed
standard form. A second cubic with (r c)³ = 1 and a common fixed line lies in
the forty-eight-element list certified in `Data`. Each listed change of basis
fixes r, normalizes the first A₄, and carries c to the canonical point cubic.
Transport of the actual generated subgroup then applies `Canonical`.

The finite identities are checked on four binary columns and transported to
actual automorphisms through an injective encoding. This supplies the marked
local action recognition needed by Aschbacher–Smith 14.3.19(4).
-/

namespace BinaryA4Pair.Normal
open FixedFreeA4BinaryData BinaryA4Pair.Data
open Subgroup
set_option maxRecDepth 4096
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
private theorem code_injective : Function.Injective code := by
  intro f g h
  apply MulEquiv.ext
  intro v
  obtain ⟨b,rfl⟩ := vector_surjective v
  rw [←apply_code f,←apply_code g]
  exact congrArg (fun c => vector (applyCode c b)) h

private theorem code_one : code (1 : Aut) = identity := by decide +kernel
private theorem code_reflection : code reflectionAut = reflection := by decide +kernel
private theorem code_cubic : code cubicAut = cubic := by decide +kernel
private theorem code_pointCubic : code pointCubicAut = (8,2,4,11) := by decide +kernel

private theorem reflection_fixed : ∀ b : B, applyCode reflection b = b ↔
    b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide +kernel

private theorem small_apply (c : Code) (b : B) (hb : applyCode reflection b = b) :
    applyCode c b = applyCode (c.1,c.2.1,0,0) b := by
  rcases (reflection_fixed b).mp hb with rfl | rfl | rfl | rfl <;> rfl

private theorem fixedLine_of_card (c : Aut)
    (hc : Nat.card {v : V // reflectionAut v = v ∧ c v = v} = 2) :
    fixedLine (code c) = true := by
  let e : B ≃ V := ⟨vector,unvector,unvector_vector,vector_unvector⟩
  have he : Nat.card {b : B // applyCode reflection b = b ∧ applyCode (code c) b = b} = 2 := by
    refine (Nat.card_congr (e.subtypeEquiv (fun b => ?_))).trans hc
    change (_ ∧ _) ↔ (reflectionAut (vector b) = vector b ∧ c (vector b) = vector b)
    rw [← code_reflection,← apply_code,← apply_code]
    exact and_congr vector_injective.eq_iff.symm vector_injective.eq_iff.symm
  have hs : Nat.card {b : B // applyCode reflection b = b ∧
      applyCode ((code c).1,(code c).2.1,0,0) b = b} = 2 := by
    refine (Nat.card_congr (Equiv.subtypeEquivRight (fun b => ?_))).trans he
    exact and_congr_right (fun hb => by rw [small_apply (code c) b hb])
  have hfinite : ∀ a b : B,
      Fintype.card {v : B // applyCode reflection v = v ∧ applyCode (a,b,0,0) v = v} = 2 ↔
        fixedLine (a,b,0,0) = true := by decide +kernel
  exact (hfinite (code c).1 (code c).2.1).mp (by rwa [← Nat.card_eq_fintype_card])

private theorem frame_left (k : Fin 48) (v : V) :
    vector (applyCode (inverseFrames k)
      (unvector (vector (applyCode (frames k) (unvector v))))) = v := by
  obtain ⟨b,rfl⟩ := vector_surjective v
  rw [unvector_vector,unvector_vector]
  exact congrArg vector ((show ∀ (k : Fin 48) (b : B),
    applyCode (inverseFrames k) (applyCode (frames k) b) = b from by decide +kernel) k b)
private theorem frame_right (k : Fin 48) (v : V) :
    vector (applyCode (frames k)
      (unvector (vector (applyCode (inverseFrames k) (unvector v))))) = v := by
  obtain ⟨b,rfl⟩ := vector_surjective v
  rw [unvector_vector,unvector_vector]
  exact congrArg vector ((show ∀ (k : Fin 48) (b : B),
    applyCode (frames k) (applyCode (inverseFrames k) b) = b from by decide +kernel) k b)
private theorem frame_mul (k : Fin 48) (v w : V) :
    vector (applyCode (frames k) (unvector (v*w))) =
      vector (applyCode (frames k) (unvector v)) *
        vector (applyCode (frames k) (unvector w)) := by
  obtain ⟨a,rfl⟩ := vector_surjective v
  obtain ⟨b,rfl⟩ := vector_surjective w
  rw [← vector_xor,unvector_vector,unvector_vector,unvector_vector,← vector_xor]
  exact congrArg vector ((show ∀ (k : Fin 48) (a b : B),
    applyCode (frames k) (xor a b) = xor (applyCode (frames k) a) (applyCode (frames k) b)
      from by decide +kernel) k a b)
private def frameAut (k : Fin 48) : Aut where
  toFun v := vector (applyCode (frames k) (unvector v))
  invFun v := vector (applyCode (inverseFrames k) (unvector v))
  left_inv := frame_left k
  right_inv := frame_right k
  map_mul' := frame_mul k
private theorem code_frame : ∀ k : Fin 48, code (frameAut k) = frames k := by decide +kernel
private theorem code_frame_inverse : ∀ k : Fin 48,
    code ((frameAut k)⁻¹) = inverseFrames k := by decide +kernel

private def firstGenerator : Fin 2 → Aut := ![reflectionAut,cubicAut]
private def firstWord (w : List (Fin 2)) : Aut := (w.map firstGenerator).prod

private def wordCode : List (Fin 2) → Code
  | [] => identity
  | k::w => mulCode (![reflection,cubic] k) (wordCode w)

private theorem code_firstWord (w : List (Fin 2)) : code (firstWord w) = wordCode w := by
  induction w with
  | nil => exact code_one
  | cons k w ih =>
    change code (firstGenerator k * firstWord w) = _
    rw [code_mul,ih]
    fin_cases k
    · change mulCode (code reflectionAut) (wordCode w) = mulCode reflection (wordCode w)
      rw [code_reflection]
    · change mulCode (code cubicAut) (wordCode w) = mulCode cubic (wordCode w)
      rw [code_cubic]

private theorem frames_reflection (k : Fin 48) :
    frameAut k * reflectionAut * (frameAut k)⁻¹ = reflectionAut := by
  apply code_injective
  rw [code_mul,code_mul,code_frame,code_frame_inverse,code_reflection]
  exact (show ∀ k : Fin 48,
    mulCode (mulCode (frames k) reflection) (inverseFrames k) = reflection from
      by decide +kernel) k
private theorem frames_cubic (k : Fin 48) :
    frameAut k * cubicAut * (frameAut k)⁻¹ = firstWord (firstWords k) := by
  apply code_injective
  rw [code_mul,code_mul,code_frame,code_frame_inverse,code_cubic,code_firstWord]
  exact (show ∀ k : Fin 48,
    mulCode (mulCode (frames k) cubic) (inverseFrames k) = wordCode (firstWords k) from
      by decide +kernel) k
private theorem inverse_frames_cubic (k : Fin 48) :
    (frameAut k)⁻¹ * cubicAut * frameAut k = firstWord (inverseWords k) := by
  apply code_injective
  rw [code_mul,code_mul,code_frame,code_frame_inverse,code_cubic,code_firstWord]
  exact (show ∀ k : Fin 48,
    mulCode (mulCode (inverseFrames k) cubic) (frames k) = wordCode (inverseWords k) from
      by decide +kernel) k

private theorem frame_pointCubic (k : Fin 48) (c : Aut) (hc : code c = candidates k) :
    frameAut k * c * (frameAut k)⁻¹ = pointCubicAut := by
  apply code_injective
  rw [code_mul,code_mul,code_frame,code_frame_inverse,hc,code_pointCubic]
  exact (show ∀ k : Fin 48,
    mulCode (mulCode (frames k) (candidates k)) (inverseFrames k) = (8,2,4,11) from
      by decide +kernel) k

private theorem firstWord_mem (w : List (Fin 2)) (X : Subgroup Aut)
    (hr : reflectionAut ∈ X) (ht : cubicAut ∈ X) : firstWord w ∈ X := by
  apply list_prod_mem
  intro x hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  fin_cases k
  · exact hr
  · exact ht


@[expose] public def pairGenerator (c : Aut) : Fin 3 → Aut := ![reflectionAut,cubicAut,c]

public theorem normalized_canonical_model (c : Aut) (hc3 : c^3 = 1)
    (hrc : (reflectionAut*c)^3 = 1)
    (hfixed : Nat.card {v : V // reflectionAut v = v ∧ c v = v} = 2) :
    HasCanonicalModel (closure (Set.range (pairGenerator c))) := by
  have code_cube (g : Aut) : code (g^3) = cube (code g) := by
    simp only [pow_succ,pow_zero,one_mul,code_mul,cube]
  have hc : cube (code c) = identity := by rw [← code_cube,hc3,code_one]
  have hrc' : cube (mulCode reflection (code c)) = identity := by
    rw [← code_reflection,← code_mul,← code_cube,hrc,code_one]
  have ha : admissible (code c) = true := by
    simp only [admissible,fixedLine_of_card c hfixed,hc,hrc',beq_self_eq_true,Bool.and_self]
  obtain ⟨k,hk⟩ := classify (code c) ha
  let f : Aut ≃* Aut := MulAut.conj (frameAut k)
  let X := closure (Set.range (pairGenerator c))
  let Y := closure (Set.range binaryGenerator)
  have hXr : reflectionAut ∈ X := subset_closure ⟨0,rfl⟩
  have hXt : cubicAut ∈ X := subset_closure ⟨1,rfl⟩
  have hXc : c ∈ X := subset_closure ⟨2,rfl⟩
  have hYr : reflectionAut ∈ Y := subset_closure ⟨0,rfl⟩
  have hYt : cubicAut ∈ Y := subset_closure ⟨1,rfl⟩
  have hYc : pointCubicAut ∈ Y := subset_closure ⟨2,rfl⟩
  have hm : X.map f.toMonoidHom = Y := by
    apply le_antisymm
    · rw [map_le_iff_le_comap]
      rw [closure_le]
      rintro g ⟨j,rfl⟩
      change frameAut k * pairGenerator c j * (frameAut k)⁻¹ ∈ Y
      fin_cases j
      · change frameAut k * reflectionAut * (frameAut k)⁻¹ ∈ Y
        rw [frames_reflection]
        exact hYr
      · change frameAut k * cubicAut * (frameAut k)⁻¹ ∈ Y
        rw [frames_cubic]
        exact firstWord_mem _ Y hYr hYt
      · change frameAut k * c * (frameAut k)⁻¹ ∈ Y
        rw [frame_pointCubic k c hk.symm]
        exact hYc
    · rw [closure_le]
      rintro g ⟨j,rfl⟩
      fin_cases j
      · exact ⟨reflectionAut,hXr,frames_reflection k⟩
      · refine ⟨firstWord (inverseWords k),firstWord_mem _ X hXr hXt,?_⟩
        change frameAut k * firstWord (inverseWords k) * (frameAut k)⁻¹ = cubicAut
        rw [← inverse_frames_cubic]
        group
      · exact ⟨c,hXc,frame_pointCubic k c hk.symm⟩
  exact ⟨frameAut k,hm⟩

public theorem normalized_recognition (c : Aut) (hc3 : c^3 = 1)
    (hrc : (reflectionAut*c)^3 = 1)
    (hfixed : Nat.card {v : V // reflectionAut v = v ∧ c v = v} = 2) :
    Nonempty (closure (Set.range (pairGenerator c)) ≃* alternatingGroup (Fin 6)) :=
  (normalized_canonical_model c hc3 hrc hfixed).recognition
end BinaryA4Pair.Normal
