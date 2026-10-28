module

public import Mathlib.GroupTheory.DoubleCoset
public import Theory.AlgebraicGroup.BNPair.Bruhat
public import Theory.AlgebraicGroup.BNPair.Reflections

/-!
Word-length separation for Tits-system double cosets.

For a Tits system, the distinguished involutions generate the quotient
`N / (B ∩ N)` as a monoid.  We measure an index by the least length of an
`S`-word and induct on a shortest word.  The exchange inclusion reduces the
leading factor to either the shortened index or the original second index;
the square/nontriviality axioms identify the zero-length case and rule out a
spurious length-zero generator.  This is the generic BN-pair ingredient used
by the later Bruhat double-coset uniqueness theorem; no Coxeter presentation
or root-theoretic normal form is assumed.

The argument is the deletion induction behind GLS3, Chapter 1, Proposition
8.2.3 (equivalently the standard BN-pair proof that `BnB = Bn'B` forces the
same quotient index).
-/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

private lemma exists_S_word (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    ∃ l : List (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N),
      (∀ s ∈ l, s ∈ T.S) ∧ l.prod = w := by
  have hw : w ∈ Submonoid.closure T.S := by
    rw [T.submonoid_closure_S_eq_top]
    exact Submonoid.mem_top w
  exact Submonoid.exists_list_of_mem_closure hw

private def WordRep (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (n : ℕ) : Prop :=
  ∃ l : List (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N),
    l.length = n ∧ (∀ s ∈ l, s ∈ T.S) ∧ l.prod = w

private lemma exists_wordRep (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : ∃ n, WordRep T w n := by
  obtain ⟨l, hl, hprod⟩ := T.exists_S_word w
  exact ⟨l.length, l, rfl, hl, hprod⟩

private noncomputable instance wordRepDecidable (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : DecidablePred (WordRep T w) :=
  Classical.decPred _

/-- The least length of a word in the distinguished involutions representing `w`. -/
public noncomputable def wordLength (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : ℕ :=
  Nat.find (T.exists_wordRep w)

/-- A shortest `S`-word representing an index. -/
public lemma wordLength_spec (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    ∃ l : List (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N),
      l.length = T.wordLength w ∧ (∀ s ∈ l, s ∈ T.S) ∧ l.prod = w := by
  simpa only [wordLength, WordRep] using Nat.find_spec (T.exists_wordRep w)

/-- Any `S`-word gives an upper bound for the quotient-index word length. -/
public lemma wordLength_le (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)
    (l : List (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N))
    (hl : ∀ s ∈ l, s ∈ T.S) (hprod : l.prod = w) :
    T.wordLength w ≤ l.length := by
  unfold wordLength
  exact Nat.find_min' (T.exists_wordRep w) ⟨l, rfl, hl, hprod⟩

public lemma wordLength_one (T : TitsSystem (X := X)) : T.wordLength 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact T.wordLength_le 1 [] (by simp) (by simp)

/-- Left multiplication by a distinguished generator changes word length by at most one. -/
public lemma wordLength_mul_left_le (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    T.wordLength (s * w) ≤ T.wordLength w + 1 := by
  obtain ⟨l, hlen, hlS, hprod⟩ := T.wordLength_spec w
  have hle := T.wordLength_le (s * w) (s :: l)
    (by simpa only [List.forall_mem_cons] using ⟨hs, hlS⟩)
    (by simp only [List.prod_cons, hprod])
  simpa only [List.length_cons, hlen, Nat.add_comm] using hle

public lemma wordLength_mem_S (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) :
    T.wordLength s = 1 := by
  have hle : T.wordLength s ≤ 1 := by
    simpa [T.wordLength_one] using T.wordLength_mul_left_le hs 1
  have hne : T.wordLength s ≠ 0 := by
    intro hz
    obtain ⟨l, hl, -, hprod⟩ := T.wordLength_spec s
    rw [hz] at hl
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst l
    apply (T.involutions s hs).1
    simpa using hprod.symm
  omega

private lemma representative_mem_doubleCoset (T : TitsSystem (X := X))
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (nw : T.N)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w) :
    (nw : X) ∈
      (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X) := by
  rw [B_mul_representativeSet_mul_B T.B T.N w nw hnw]
  exact DoubleCoset.mem_doubleCoset_self T.B T.B (nw : X)

private lemma doubleCoset_eq_of_mem_both (T : TitsSystem (X := X))
    {w v : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} {x : X}
    (hw : x ∈ (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X))
    (hv : x ∈ (T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X)) :
    (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X) =
      (T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X) := by
  obtain ⟨nw, hnw⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) w
  obtain ⟨nv, hnv⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) v
  have hwd := (B_mul_representativeSet_mul_B T.B T.N w nw hnw).symm ▸ hw
  have hvd := (B_mul_representativeSet_mul_B T.B T.N v nv hnv).symm ▸ hv
  rw [B_mul_representativeSet_mul_B T.B T.N w nw hnw,
    B_mul_representativeSet_mul_B T.B T.N v nv hnv]
  apply DoubleCoset.eq_of_not_disjoint
  rw [Set.not_disjoint_iff]
  exact ⟨x, hwd, hvd⟩

private lemma wordLength_tail_eq (T : TitsSystem (X := X))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    {l : List (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)}
    (hs : s ∈ T.S) (hlS : ∀ t ∈ l, t ∈ T.S)
    (hmin : (s :: l).length = T.wordLength ((s :: l).prod)) :
    T.wordLength l.prod = l.length := by
  have hupper : T.wordLength l.prod ≤ l.length := T.wordLength_le l.prod l hlS rfl
  obtain ⟨r, hrlen, hrS, hrprod⟩ := T.wordLength_spec l.prod
  have hlower : T.wordLength ((s :: l).prod) ≤ (s :: r).length := by
    apply T.wordLength_le ((s :: l).prod) (s :: r)
    · simpa only [List.forall_mem_cons] using ⟨hs, hrS⟩
    · simp only [List.prod_cons, hrprod]
  have hlower' : (s :: l).length ≤ (s :: r).length := by
    simpa only [hmin] using hlower
  simp only [List.length_cons, hrlen] at hlower'
  simp only [List.length_cons] at hmin
  rw [hmin] at hlower'
  omega

/--
If one double coset index has no greater word length than another, a common
element forces the indices to agree.  The proof is the generic BN-pair
exchange/deletion induction and is the exact reusable input for Bruhat index
uniqueness.
-/
public theorem eq_of_mem_doubleCosets_of_wordLength_le (T : TitsSystem (X := X))
    {w v : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} {x : X}
    (hlen : T.wordLength w ≤ T.wordLength v)
    (hw : x ∈ (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X))
    (hv : x ∈ (T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X)) :
    w = v := by
  generalize hn : T.wordLength w = n at hlen ⊢
  induction n using Nat.strong_induction_on generalizing w v x with
  | h n ih =>
    by_cases hn0 : n = 0
    · obtain ⟨l, hllen, -, hlprod⟩ := T.wordLength_spec w
      rw [hn, hn0] at hllen
      have hl : l = [] := List.eq_nil_of_length_eq_zero hllen
      subst l
      simp only [List.prod_nil] at hlprod
      subst w
      have hcoset := T.doubleCoset_eq_of_mem_both hw hv
      rw [doubleCoset_one_eq_B] at hcoset
      obtain ⟨nv, hnv⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) v
      have hnvD := T.representative_mem_doubleCoset v nv hnv
      have hnvB : (nv : X) ∈ T.B := by
        change (nv : X) ∈ (T.B : Set X)
        exact hcoset.symm ▸ hnvD
      have hnvH : nv ∈ (T.B ⊓ T.N).subgroupOf T.N := by
        change (nv : X) ∈ T.B ⊓ T.N
        exact ⟨hnvB, nv.property⟩
      have hmk : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nv = 1 :=
        (QuotientGroup.eq_one_iff nv).2 hnvH
      exact hmk.symm.trans hnv
    ·
      obtain ⟨l, hllen, hlS, hlprod⟩ := T.wordLength_spec w
      rw [hn] at hllen
      obtain ⟨s, r, hlcons⟩ : ∃ s r, l = s :: r := by
        cases l with
        | nil => exact False.elim (hn0 (by simpa using hllen.symm))
        | cons s r => exact ⟨s, r, rfl⟩
      subst l
      have hs : s ∈ T.S := hlS s (by simp)
      have hrS : ∀ t ∈ r, t ∈ T.S := by
        intro t ht
        exact hlS t (by simp [ht])
      have hlenr : r.length + 1 = n := by simpa only [List.length_cons] using hllen
      have hwr : w = s * r.prod := by simpa only [List.prod_cons] using hlprod.symm
      have htail : T.wordLength r.prod = r.length := by
        apply T.wordLength_tail_eq hs hrS
        calc
          (s :: r).length = n := hllen
          _ = T.wordLength w := hn.symm
          _ = T.wordLength ((s :: r).prod) := by rw [hlprod]
      have hrword : T.wordLength r.prod = r.length := htail
      obtain ⟨ns, hns⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) s
      obtain ⟨nr, hnr⟩ := QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) r.prod
      have hnsnr : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (ns * nr) = w := by
        rw [map_mul, hns, hnr, ← hwr]
      have hzW := T.representative_mem_doubleCoset w (ns * nr) hnsnr
      have hzV : ((ns * nr : T.N) : X) ∈
          (T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X) := by
        have hcoset := T.doubleCoset_eq_of_mem_both hw hv
        rw [← hcoset]
        exact hzW
      let y : X := (ns : X) * ((ns * nr : T.N) : X)
      have hnsD := T.representative_mem_doubleCoset s ns hns
      have hyProduct : y ∈
          ((T.B : Set X) * representativeSet T.B T.N s * (T.B : Set X)) *
            ((T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X)) := by
        exact ⟨(ns : X), hnsD, ((ns * nr : T.N) : X), hzV, rfl⟩
      have hsq := T.representative_sq_mem_intersection hs ns hns
      have hsqB : ((ns ^ 2 : T.N) : X) ∈ T.B := by
        change ((ns ^ 2 : T.N) : X) ∈ T.B ⊓ T.N at hsq
        exact hsq.1
      have hyR : y ∈
          (T.B : Set X) * representativeSet T.B T.N r.prod * (T.B : Set X) := by
        have hnrD := T.representative_mem_doubleCoset r.prod nr hnr
        change (ns : X) * ((ns * nr : T.N) : X) ∈ _
        simpa only [Subgroup.coe_mul, pow_two, mul_assoc, mul_one] using
          mul_mem_doubleCoset T.B T.N r.prod hsqB T.B.one_mem hnrD
      rcases doubleCoset_mul_doubleCoset_subset_of_mem_S T hs v hyProduct with hsv | hv'
      · have hlenSV : T.wordLength r.prod ≤ T.wordLength (s * v) := by
          have hback : T.wordLength v ≤ T.wordLength (s * v) + 1 := by
            have h := T.wordLength_mul_left_le hs (s * v)
            have hs2 : s * s = (1 : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) := by
              simpa only [pow_two] using (T.involutions s hs).2
            simpa only [← mul_assoc, hs2, one_mul] using h
          have hlen' : n ≤ T.wordLength v := hlen
          rw [hrword]
          omega
        have hrEq : r.prod = s * v := by
          apply ih (r.length) (by omega) (x := y)
          · exact hyR
          · exact hsv
          · exact hrword
          · rw [← hrword]
            exact hlenSV
        rw [hwr, hrEq, ← mul_assoc, show s * s = (1 : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) by
          simpa only [pow_two] using (T.involutions s hs).2, one_mul]
      · have hrEq : r.prod = v := by
          apply ih (r.length) (by omega) (x := y)
          · exact hyR
          · exact hv'
          · exact hrword
          · omega
        have heqLen : T.wordLength r.prod = T.wordLength v :=
          congrArg T.wordLength hrEq
        rw [hrword] at heqLen
        omega

end Theory.AlgebraicGroup.TitsSystem
