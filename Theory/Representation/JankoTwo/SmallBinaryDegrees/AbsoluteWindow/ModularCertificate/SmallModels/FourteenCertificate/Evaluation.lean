module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.RankOne

/-!
# Evaluation tools for the degree-fourteen certificate

Finite four-element products are transported to an arbitrary characteristic-two
field. The algebra combination uses the displayed positive words, and the
polynomial uses constant-first Horner evaluation. Closure of these operations
in a subalgebra connects the numerical rank-one witness to the density theorem.
Source: the ATLAS witnesses retained in ../source/.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

theorem product_eq (t : F) (ht : t ^ 2 = t + 1)
    (M N R : CodeMatrix n) (h : codeProduct M N = R) :
    evalMatrix t M * evalMatrix t N = evalMatrix t R := by
  rw [← eval_product t ht, h]

omit [CharP F 2] in
theorem word_nil (A B : Matrix (Fin n) (Fin n) F) : wordValue A B [] = 1 := rfl

omit [CharP F 2] in
theorem word_cons (A B : Matrix (Fin n) (Fin n) F) (s : Bool) (w : List Bool) :
    wordValue A B (s :: w) = (if s then B else A) * wordValue A B w := rfl

omit [CharP F 2] in
theorem word_singleton (A B : Matrix (Fin n) (Fin n) F) (s : Bool) :
    wordValue A B [s] = if s then B else A := by rw [word_cons, word_nil, mul_one]

omit [CharP F 2] in
theorem word_append (A B : Matrix (Fin n) (Fin n) F) (u w : List Bool) :
    wordValue A B (u ++ w) = wordValue A B u * wordValue A B w := by
  simp only [wordValue, List.map_append, List.prod_append]

/-- The supplied linear combination of algebra words, with their literal order. -/
def algebraValue (t : F) (A B : Matrix (Fin n) (Fin n) F) :
    List (Fin 4) → List (List Bool) → Matrix (Fin n) (Fin n) F
  | c :: cs, w :: ws => coefficient t c • wordValue A B w + algebraValue t A B cs ws
  | _, _ => 0

omit [CharP F 2] in
theorem algebraValue_mem (t : F) (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (A B : Matrix (Fin n) (Fin n) F) (hA : A ∈ S) (hB : B ∈ S)
    (cs : List (Fin 4)) (ws : List (List Bool)) : algebraValue t A B cs ws ∈ S := by
  induction cs generalizing ws with
  | nil => exact S.zero_mem
  | cons c cs ih =>
    cases ws with
    | nil => exact S.zero_mem
    | cons w ws => exact S.add_mem (S.smul_mem (wordValue_mem S A B hA hB w) _) (ih ws)

/-- Constant-first polynomial evaluation. -/
def polynomialValue (t : F) (T : Matrix (Fin n) (Fin n) F) :
    List (Fin 4) → Matrix (Fin n) (Fin n) F
  | [] => 0
  | c :: cs => coefficient t c • 1 + T * polynomialValue t T cs

omit [CharP F 2] in
theorem polynomialValue_mem (t : F) (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (T : Matrix (Fin n) (Fin n) F) (hT : T ∈ S) (cs : List (Fin 4)) :
    polynomialValue t T cs ∈ S := by
  induction cs with
  | nil => exact S.zero_mem
  | cons c cs ih => exact S.add_mem (S.smul_mem S.one_mem _) (S.mul_mem hT ih)

theorem horner_step (t : F) (ht : t ^ 2 = t + 1) (c : Fin 4)
    (T N R : CodeMatrix n) (h : codeAdd (codeScale c codeOne) (codeProduct T N) = R) :
    coefficient t c • (1 : Matrix (Fin n) (Fin n) F) +
      evalMatrix t T * evalMatrix t N = evalMatrix t R := by
  rw [← eval_product t ht, ← eval_one t, ← eval_scale t ht, ← eval_add t, h]

theorem left_step (t : F) (ht : t ^ 2 = t + 1) (A B : CodeMatrix n)
    (v x y : CodeVector n) (s : Bool) (w : List Bool)
    (h : (wordValue (evalMatrix t A) (evalMatrix t B) w).mulVec (evalVector t v) =
      evalVector t x)
    (hc : codeMulVec (if s then B else A) x = y) :
    (wordValue (evalMatrix t A) (evalMatrix t B) (s :: w)).mulVec (evalVector t v) =
      evalVector t y := by
  rw [word_cons, ← Matrix.mulVec_mulVec, h]
  cases s <;> exact (eval_mulVec t ht _ x).symm.trans (congrArg (evalVector t) hc)

theorem right_step (t : F) (ht : t ^ 2 = t + 1) (A B : CodeMatrix n)
    (lam x y : CodeVector n) (w : List Bool) (s : Bool)
    (h : Matrix.vecMul (evalVector t lam) (wordValue (evalMatrix t A) (evalMatrix t B) w) =
      evalVector t x)
    (hc : codeVecMul x (if s then B else A) = y) :
    Matrix.vecMul (evalVector t lam)
      (wordValue (evalMatrix t A) (evalMatrix t B) (w ++ [s])) = evalVector t y := by
  rw [word_append, word_singleton, ← Matrix.vecMul_vecMul, h]
  cases s <;> exact (eval_vecMul t ht x _).symm.trans (congrArg (evalVector t) hc)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
