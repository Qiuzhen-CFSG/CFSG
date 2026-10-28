module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Reordering filtered coefficient words

If a commutator is a linear combination of words of smaller total degree,
strong induction permits any permutation of a word modulo an already chosen
normal-form span. This elementary filtered-algebra argument does not assume
linear independence or a representation classification.

It is used for the truncated root coefficients in Steinberg's root-monomial
construction (1963, section 2).
-/

open scoped Pointwise
namespace CoefficientPBW
variable {k A I : Type*} [Field k] [Ring A] [Algebra k A]
@[expose] public noncomputable section
def wordValue (X:I→A) (w:List I) : A := (w.map X).prod
def wordDegree (d:I→ℕ) (w:List I) : ℕ := (w.map d).sum
@[simp] lemma wordValue_nil (X:I→A) : wordValue X []=1 := rfl
@[simp] lemma wordValue_cons (X:I→A) (a:I) (w:List I) : wordValue X (a::w)=X a*wordValue X w := rfl
@[simp] lemma wordValue_append (X:I→A) (w z:List I) : wordValue X (w++z)=wordValue X w*wordValue X z := by simp [wordValue]
@[simp] lemma wordDegree_nil (d:I→ℕ) : wordDegree d []=0 := rfl
@[simp] lemma wordDegree_cons (d:I→ℕ) (a:I) (w:List I) : wordDegree d (a::w)=d a+wordDegree d w := rfl
@[simp] lemma wordDegree_append (d:I→ℕ) (w z:List I) : wordDegree d (w++z)=wordDegree d w+wordDegree d z := by simp [wordDegree]
lemma wordDegree_perm (d:I→ℕ) {w z:List I} (h:w.Perm z) : wordDegree d w=wordDegree d z := (h.map d).sum_eq

def lowerWords (X:I→A) (d:I→ℕ) (n:ℕ) : Submodule k A :=
  Submodule.span k {x | ∃ w:List I, wordDegree d w<n ∧ wordValue X w=x}

lemma perm_value_mod (X:I→A) (d:I→ℕ) (U:Submodule k A) (n:ℕ)
    (hs : ∀(p s:List I) (a b:I), wordDegree d (p++a::b::s)≤n →
      U.mkQ (wordValue X (p++a::b::s))=U.mkQ (wordValue X (p++b::a::s)))
    {w z:List I} (h:w.Perm z) :
    ∀(p s:List I),wordDegree d (p++w++s)≤n →
      U.mkQ (wordValue X (p++w++s))=U.mkQ (wordValue X (p++z++s)) := by
  induction h with
  | nil => intro p s hn; rfl
  | @cons a w z h ih =>
    intro p s hn
    simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using ih (p++[a]) s
      (by simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using hn)
  | swap a b w =>
    intro p s hn
    simpa only [List.append_assoc,List.cons_append] using hs p (w++s) b a
      (by simpa only [List.append_assoc,List.cons_append] using hn)
  | @trans w z t h₁ h₂ ih₁ ih₂ =>
    intro p s hn
    exact (ih₁ p s hn).trans (ih₂ p s (by simpa only [wordDegree_append,←wordDegree_perm d h₁] using hn))

lemma word_mem_of_reordering (X:I→A) (d:I→ℕ) (U:Submodule k A)
    (hc:∀a b,X a*X b-X b*X a ∈ lowerWords (k:=k) X d (d a+d b))
    (hnormal:∀w:List I,∃z,w.Perm z ∧ wordValue X z∈U) (w:List I) : wordValue X w∈U := by
  have allwords : ∀ n, ∀w:List I,wordDegree d w=n → wordValue X w∈U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      have context (p s:List I) (a b:I) (hn:wordDegree d (p++a::b::s)≤n) :
          wordValue X p*(X a*X b-X b*X a)*wordValue X s∈U := by
        have hl := hc a b
        generalize he : X a*X b-X b*X a = x at hl ⊢
        clear he
        induction hl using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z,hz,rfl⟩ := hx
          have hm : wordDegree d (p++z++s)<n := by
            simp only [wordDegree_append,wordDegree_cons] at hn ⊢
            omega
          simpa only [wordValue_append] using ih _ hm (p++z++s) rfl
        | zero => simpa only [mul_zero,zero_mul] using U.zero_mem
        | add x y _ _ hx hy => simpa only [mul_add,add_mul] using U.add_mem hx hy
        | smul c x _ hx => simpa only [mul_smul_comm,smul_mul_assoc] using U.smul_mem c hx
      have hs (p s:List I) (a b:I) (hn:wordDegree d (p++a::b::s)≤n) :
          U.mkQ (wordValue X (p++a::b::s))=U.mkQ (wordValue X (p++b::a::s)) := by
        apply (Submodule.Quotient.eq U).mpr
        convert context p s a b hn using 1
        simp only [wordValue_append,wordValue_cons]
        noncomm_ring
      obtain ⟨z,hz,hzu⟩ := hnormal w
      have he := perm_value_mod X d U n hs hz [] [] (by simpa using hw.le)
      have he' : U.mkQ (wordValue X w)=U.mkQ (wordValue X z) := by
        simpa only [List.nil_append,List.append_nil] using he
      have hz0 : U.mkQ (wordValue X z)=0 := (Submodule.Quotient.mk_eq_zero U).mpr hzu
      exact (Submodule.Quotient.mk_eq_zero U).mp (he'.trans hz0)
  exact allwords _ w rfl
lemma adjoin_le_of_words (X:I→A) (U:Submodule k A)
    (hw:∀w:List I,wordValue X w∈U) : (Algebra.adjoin k (Set.range X)).toSubmodule≤U := by
  apply (Algebra.adjoin_toSubmodule_le k).mpr
  intro x hx
  have hex : ∃w:List I,wordValue X w=x := by
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      exact ⟨[a],by simp⟩
    | one => exact ⟨[],rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w,rfl⟩ := hx
      obtain ⟨z,rfl⟩ := hy
      exact ⟨w++z,wordValue_append X w z⟩
  obtain ⟨w,rfl⟩ := hex
  exact hw w

end
end CoefficientPBW
