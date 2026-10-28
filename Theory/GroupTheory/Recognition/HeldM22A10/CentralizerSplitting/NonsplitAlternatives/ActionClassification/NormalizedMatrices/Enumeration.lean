module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.NormalizedMatrices.Encoding
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
/-!
# Exhaustive normalized column certificates

Commutation determines one column from the other three, leaving at most
4096 candidates for each transposition matrix. Kernel reduction checks the
remaining group relations and both fixed counts. There are three surviving
ordinary matrices and four surviving twisted matrices. The reconstruction
lemmas ensure that this search covers every four-column matrix satisfying
the hypotheses; no enumeration is assumed.

The finite tables are auxiliary computations for the action problem supporting
Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
private theorem xor_zero (a : Fin 16) : a ^^^ 0 = a := by
  have h : ∀ a : Fin 16, a ^^^ 0 = a := by decide +kernel
  exact h a
private theorem zero_xor (a : Fin 16) : 0 ^^^ a = a := by
  have h : ∀ a : Fin 16, 0 ^^^ a = a := by decide +kernel
  exact h a
private theorem app_two (k : Cols) : app k 2 = k 1 := by simp [app, xor_zero, zero_xor]
private theorem app_thirteen (k : Cols) : app k 13 = k 0 ^^^ k 2 ^^^ k 3 := by simp [app, xor_zero]
private theorem t_reconstruct (k : Cols) (h : comp t k = comp k t) :
    k = ![k 0, app t (k 0), k 2, k 3] := by
  have h1 := congrFun h 0
  change app t (k 0) = app k 2 at h1
  rw [app_two] at h1
  ext i
  fin_cases i <;> simp [h1]
private theorem u_reconstruct (k : Cols) (h : comp u k = comp k u) :
    k = ![k 0, k 1, k 2, app u (k 0) ^^^ k 0 ^^^ k 2] := by
  have h1 := congrFun h 0
  change app u (k 0) = app k 13 at h1
  rw [app_thirteen] at h1
  have hxor : ∀ a c d : Fin 16, (a ^^^ c ^^^ d) ^^^ a ^^^ c = d := by decide +kernel
  have hd : app u (k 0) ^^^ k 0 ^^^ k 2 = k 3 := by rw [h1, hxor]
  ext i
  fin_cases i <;> simp [hd]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t_certificate : ∀ a c d : Fin 16, let k : Cols := ![a,app t a,c,d];
    rels t k → fixedCount x t k = 2 → fixedCount t k (comp x (comp k xi)) = 2 →
    k = ![2,1,8,4] ∨ k = ![2,1,15,8] ∨ k = ![6,5,4,12] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem u_certificate : ∀ a b c : Fin 16, let k : Cols := ![a,b,c,app u a ^^^ a ^^^ c];
    rels u k → fixedCount x u k = 2 → fixedCount u k (comp x (comp k xi)) = 2 →
    k = ![2,1,8,4] ∨ k = ![6,10,11,8] ∨ k = ![9,5,11,8] ∨ k = ![14,13,4,8] := by decide +kernel
public theorem ordinary_cases (k : Cols) (hr : rels t k)
    (hf : fixedCount x t k = 2) (hs : fixedCount t k (comp x (comp k xi)) = 2) :
    k = ![2,1,8,4] ∨ k = ![2,1,15,8] ∨ k = ![6,5,4,12] := by
  have hk := t_reconstruct k hr.2.1
  have h := t_certificate (k 0) (k 2) (k 3)
  dsimp only at h
  rw [← hk] at h
  exact h hr hf hs
public theorem twisted_cases (k : Cols) (hr : rels u k)
    (hf : fixedCount x u k = 2) (hs : fixedCount u k (comp x (comp k xi)) = 2) :
    k = ![2,1,8,4] ∨ k = ![6,10,11,8] ∨ k = ![9,5,11,8] ∨ k = ![14,13,4,8] := by
  have hk := u_reconstruct k hr.2.1
  have h := u_certificate (k 0) (k 1) (k 2)
  dsimp only at h
  rw [← hk] at h
  exact h hr hf hs
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
