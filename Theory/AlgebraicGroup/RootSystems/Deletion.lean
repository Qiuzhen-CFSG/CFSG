module

public import Theory.AlgebraicGroup.RootSystems.Matsumoto

/-! Reduction of Weyl-group words by Coxeter braid and cancellation moves. -/

namespace Theory.AlgebraicGroup

/-- Every simple-reflection word reduces by Coxeter moves to a reduced word
with the same Weyl-group product. -/
public lemma _root_.RootPairing.Base.exists_reducedWord_reflTransGen_coxeterMove
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (l : List b.support) :
    ∃ r : List b.support,
      b.wordProd r = b.wordProd l ∧
      r.length = b.wordLength (b.wordProd r) ∧
      Relation.ReflTransGen (CoxeterMove C) l r := by
  induction l using List.reverseRecOn with
  | nil =>
      exact ⟨[], rfl, by simp, Relation.ReflTransGen.refl⟩
  | append_singleton l i ih =>
      rcases ih with ⟨r, hrprod, hrred, hpath⟩
      have hpathApp := coxeterMove_reflTransGen_append_right
        C [i] hpath
      have hprodApp : b.wordProd (r ++ [i]) =
          b.wordProd (l ++ [i]) := by
        simp only [b.wordProd_append, hrprod]
      by_cases hpos : b.IsPos (P.weylGroupToPerm (b.wordProd r) i)
      · refine ⟨r ++ [i], hprodApp, ?_, hpathApp⟩
        simp only [List.length_append, List.length_singleton,
          b.wordProd_append, b.wordProd_cons, b.wordProd_nil, mul_one]
        rw [b.wordLength_mul_simpleReflection_of_isPos _ _ hpos, ← hrred]
      · obtain ⟨q, hqlen, hqprod⟩ :=
          b.wordLength_spec (b.wordProd r * b.simpleReflection i)
        have hdec := b.wordLength_mul_simpleReflection_of_not_isPos
          (b.wordProd r) i hpos
        have hqAppendProd : b.wordProd (q ++ [i]) = b.wordProd r := by
          rw [b.wordProd_append, hqprod]
          simp [mul_assoc]
        have hqAppendRed : (q ++ [i]).length =
            b.wordLength (b.wordProd (q ++ [i])) := by
          rw [hqAppendProd]
          simp only [List.length_append, List.length_singleton, hqlen]
          exact hdec
        have hbraid := b.reducedWords_reflTransGen_coxeterMove
          C hC r (q ++ [i]) hqAppendProd.symm hrred hqAppendRed
        have hbraidApp := coxeterMove_reflTransGen_append_right
          C [i] hbraid
        have hbraidApp' : Relation.ReflTransGen (CoxeterMove C)
            (r ++ [i]) (q ++ [i, i]) := by
          simpa [List.append_assoc] using hbraidApp
        have hcancel : CoxeterMove C (q ++ [i, i]) q := by
          simpa using coxeterMove_cancel C q [] i
        have hqprodInput : b.wordProd q =
            b.wordProd (l ++ [i]) := by
          calc
            b.wordProd q = b.wordProd r * b.simpleReflection i := hqprod
            _ = b.wordProd (r ++ [i]) := by simp
            _ = b.wordProd (l ++ [i]) := hprodApp
        have hqred : q.length = b.wordLength (b.wordProd q) := by
          rw [hqprod]
          exact hqlen
        exact ⟨q, hqprodInput, hqred,
          hpathApp.trans (hbraidApp'.trans
            (Relation.ReflTransGen.single hcancel))⟩

/-- A simple-reflection word with Weyl-group product one reduces to the empty
word by Coxeter braid and cancellation moves. -/
public theorem _root_.RootPairing.Base.wordProd_one_reflTransGen_nil
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (l : List b.support) (hl : b.wordProd l = 1) :
    Relation.ReflTransGen (CoxeterMove C) l [] := by
  obtain ⟨r, hrprod, hrred, hpath⟩ :=
    b.exists_reducedWord_reflTransGen_coxeterMove C hC l
  have hrprodOne : b.wordProd r = 1 := hrprod.trans hl
  have hrlen : r.length = 0 := by
    rw [hrred, hrprodOne, b.wordLength_one]
  have hrnil : r = [] := List.length_eq_zero_iff.mp hrlen
  simpa only [hrnil] using hpath

end Theory.AlgebraicGroup
