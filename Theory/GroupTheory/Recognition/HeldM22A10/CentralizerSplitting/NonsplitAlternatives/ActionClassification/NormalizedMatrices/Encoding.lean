module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open scoped BigOperators
/-!
# Binary column arithmetic for normalized S₄ actions

Four columns in `Fin 16` encode an endomorphism of the binary four-space.
Xor computes vector addition; the decoding and composition lemmas identify
this arithmetic with actual multiplicative homomorphisms. Fixed counts are
transported through a proved equivalence of the sixteen vectors.

This is a computational coordinate layer for the independent action problem
supporting Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
No completeness of the action models is assumed here.
-/
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
public abbrev Cols := Fin 4 → Fin 16
private def decode (v : Fin 16) : BinaryFour :=
  Multiplicative.ofAdd (fun i => ((v.val / 2 ^ i.val % 2 : ℕ) : ZMod 2))
@[expose] public def lin (k : Cols) (v : BinaryFour) : BinaryFour := matrixActionFun (fun _ => k) 1 v
public theorem lin_mul (k : Cols) (v w : BinaryFour) : lin k (v*w) = lin k v * lin k w :=
  congrArg Multiplicative.ofAdd (Matrix.mulVec_add _ _ _)
private theorem lin_basis (k : Cols) (i : Fin 4) : lin k (binaryBasis i) = decode (k i) := by
  change Multiplicative.ofAdd ((coefficientMatrix (fun _ => k) 1).mulVec (Pi.single i 1)) = _
  rw [Matrix.mulVec_single_one]
  rfl
private noncomputable def codeEquiv : Fin 16 ≃ BinaryFour := Equiv.ofBijective decode (by decide +kernel)
@[expose] public def app (k : Cols) (v : Fin 16) : Fin 16 :=
  (if v.val % 2 = 1 then k 0 else 0) ^^^
  (if v.val / 2 % 2 = 1 then k 1 else 0) ^^^
  (if v.val / 4 % 2 = 1 then k 2 else 0) ^^^
  (if v.val / 8 % 2 = 1 then k 3 else 0)
@[expose] public def comp (k l : Cols) : Cols := fun i => app k (l i)
@[expose] public def ident : Cols := ![1,2,4,8]
@[expose] public def x : Cols := ![2,4,1,8]
@[expose] public def xi : Cols := ![4,1,2,8]
@[expose] public def t : Cols := ![2,1,4,8]
@[expose] public def u : Cols := ![13,14,11,7]
@[expose] public def rels (T k : Cols) : Prop := comp k k = ident ∧ comp T k = comp k T ∧
  comp k (comp x (comp k xi)) = comp xi (comp k x)
public instance (T k : Cols) : Decidable (rels T k) := inferInstanceAs (Decidable (_ ∧ _))
private def linHom (k : Cols) : BinaryFour →* BinaryFour where
  toFun := lin k
  map_one' := by
    change Multiplicative.ofAdd ((coefficientMatrix (fun _ => k) 1).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' := lin_mul k
private theorem lin_expansion (k : Cols) (v : BinaryFour) :
    lin k v = ∏ i : Fin 4, decode (k i) ^ (v.toAdd i).val := by
  change linHom k v = _
  conv_lhs => rw [binaryBasis_expansion v]
  rw [map_prod]
  simp only [map_pow, show ∀ i, linHom k (binaryBasis i) = decode (k i) from lin_basis k]
private theorem decode_xor (a b : Fin 16) : decode (a ^^^ b) = decode a * decode b := by
  have h : ∀ a b : Fin 16, decode (a ^^^ b) = decode a * decode b := by decide +kernel
  exact h a b
private theorem decode_zero : decode 0 = 1 := by decide +kernel
private theorem decode_coord (v : Fin 16) (i : Fin 4) :
    (decode v).toAdd i = ((v.val / 2 ^ i.val % 2 : ℕ) : ZMod 2) := rfl
private theorem app_correct (k : Cols) (v : Fin 16) : decode (app k v) = lin k (decode v) := by
  rw [lin_expansion]
  simp only [app, decode_xor]
  fin_cases v <;> norm_num [decode_coord, decode_zero, Fin.prod_univ_succ, mul_assoc] <;> rfl
@[expose] public def fixedCount (a b c : Cols) : ℕ :=
  (Finset.univ.filter (fun v : Fin 16 => app a v = v ∧ app b v = v ∧ app c v = v)).card
private theorem linHom_ext (e f : BinaryFour →* BinaryFour)
    (h : ∀ i, e (binaryBasis i) = f (binaryBasis i)) : e = f := by
  apply MonoidHom.ext
  intro v
  conv_lhs => rw [binaryBasis_expansion v]
  conv_rhs => rw [binaryBasis_expansion v]
  simp only [map_prod, map_pow, h]
public theorem lin_comp (k l : Cols) (v : BinaryFour) : lin (comp k l) v = lin k (lin l v) := by
  have h : linHom (comp k l) = (linHom k).comp (linHom l) := by
    apply linHom_ext
    intro i
    change lin (comp k l) (binaryBasis i) = lin k (lin l (binaryBasis i))
    rw [lin_basis, lin_basis]
    exact app_correct k (l i)
  exact congrArg (fun f : BinaryFour →* BinaryFour => f v) h
public theorem lin_injective : Function.Injective lin := by
  intro k l h
  funext i
  apply codeEquiv.injective
  change decode (k i) = decode (l i)
  rw [← lin_basis, ← lin_basis, h]
public noncomputable def columns (e : MulAut BinaryFour) : Cols :=
  fun i => codeEquiv.symm (e (binaryBasis i))
public theorem lin_columns (e : MulAut BinaryFour) (v : BinaryFour) : lin (columns e) v = e v := by
  have h : linHom (columns e) = e.toMonoidHom := by
    apply linHom_ext
    intro i
    change lin (columns e) (binaryBasis i) = e (binaryBasis i)
    rw [lin_basis]
    exact codeEquiv.apply_symm_apply _
  exact congrArg (fun f : BinaryFour →* BinaryFour => f v) h
public theorem columns_mul (e f : MulAut BinaryFour) : columns (e * f) = comp (columns e) (columns f) := by
  apply lin_injective
  funext v
  rw [lin_columns, lin_comp, lin_columns, lin_columns]
  rfl
public theorem lin_ident (v : BinaryFour) : lin ident v = v := by
  have h : ∀ v, lin ident v = v := by decide +kernel
  exact h v
public theorem columns_one : columns 1 = ident := by
  apply lin_injective
  funext v
  rw [lin_columns, lin_ident]
  rfl
public theorem fixedCount_eq (a b c : Cols) : fixedCount a b c =
    Nat.card {v : BinaryFour // lin a v = v ∧ lin b v = v ∧ lin c v = v} := by
  let e : {v : Fin 16 // app a v = v ∧ app b v = v ∧ app c v = v} ≃
      {v : BinaryFour // lin a v = v ∧ lin b v = v ∧ lin c v = v} :=
    codeEquiv.subtypeEquiv (by
      intro v
      change (app a v = v ∧ app b v = v ∧ app c v = v) ↔
        (lin a (decode v) = decode v ∧ lin b (decode v) = decode v ∧ lin c (decode v) = decode v)
      have hd : Function.Injective decode := codeEquiv.injective
      simp only [← app_correct, hd.eq_iff])
  calc
    fixedCount a b c = Nat.card {v : Fin 16 // app a v = v ∧ app b v = v ∧ app c v = v} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    _ = _ := Nat.card_congr e
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
