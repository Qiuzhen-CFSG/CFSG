module

public import Theory.AlgebraicGroup.RootSystems.RankTwoBraid

/-! Braid connectivity of reduced Weyl-group words. -/

namespace Theory.AlgebraicGroup

private lemma reduced_dropLast
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support) (hne : l ≠ [])
    (hred : l.length = b.wordLength (b.wordProd l)) :
    l.dropLast.length = b.wordLength (b.wordProd l.dropLast) := by
  let i : b.support := l.getLast hne
  have hdecomp : l.dropLast ++ [i] = l :=
    List.dropLast_append_getLast hne
  have hle : b.wordLength (b.wordProd l.dropLast) ≤ l.dropLast.length :=
    b.wordLength_le _ l.dropLast rfl
  have hall := b.wordLength_mul_simpleReflection_le
    (b.wordProd l.dropLast) i
  have hprod : b.wordProd (l.dropLast ++ [i]) =
      b.wordProd l.dropLast * b.simpleReflection i := by simp
  rw [← hprod, hdecomp, ← hred] at hall
  have hlen : l.dropLast.length + 1 = l.length := by
    rw [← hdecomp]
    simp
  omega

private lemma reduced_prefix_of_append_singleton
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support) (i : b.support)
    (hred : (l ++ [i]).length =
      b.wordLength (b.wordProd (l ++ [i]))) :
    l.length = b.wordLength (b.wordProd l) := by
  have hle : b.wordLength (b.wordProd l) ≤ l.length :=
    b.wordLength_le _ l rfl
  have hall := b.wordLength_mul_simpleReflection_le (b.wordProd l) i
  have hprod : b.wordProd (l ++ [i]) =
      b.wordProd l * b.simpleReflection i := by simp
  rw [← hprod, ← hred] at hall
  simp only [List.length_append, List.length_singleton] at hall
  omega

private lemma wordProd_prefix_eq_append_singleton_mul
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N}
    (b : P.Base) (l : List b.support) (i : b.support) :
    b.wordProd l = b.wordProd (l ++ [i]) * b.simpleReflection i := by
  rw [b.wordProd_append]
  simp [mul_assoc]

private lemma wordProd_dropLast_eq_mul_last
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N}
    (b : P.Base) (l : List b.support) (hne : l ≠ []) :
    b.wordProd l.dropLast =
      b.wordProd l * b.simpleReflection (l.getLast hne) := by
  have hdecomp : l.dropLast ++ [l.getLast hne] = l :=
    List.dropLast_append_getLast hne
  have hfull : b.wordProd l = b.wordProd l.dropLast *
      b.simpleReflection (l.getLast hne) := by
    calc
      b.wordProd l = b.wordProd (l.dropLast ++ [l.getLast hne]) :=
        congrArg b.wordProd hdecomp.symm
      _ = b.wordProd l.dropLast *
          b.simpleReflection (l.getLast hne) := by simp
  calc
    b.wordProd l.dropLast =
        (b.wordProd l.dropLast * b.simpleReflection (l.getLast hne)) *
          b.simpleReflection (l.getLast hne) := by simp [mul_assoc]
    _ = b.wordProd l * b.simpleReflection (l.getLast hne) := by rw [hfull]

set_option maxHeartbeats 800000 in
private lemma coxeterMatrix_apply_pos_of_orders_of_ne
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) (hij : i ≠ j) :
    0 < C i j := by
  have hiC := b.cartanMatrix_mem_of_ne hij
  have hjC := b.cartanMatrix_mem_of_ne (Ne.symm hij)
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  change (b.cartanMatrix i j, b.cartanMatrix j i) ∈
    ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2),
      (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1), (2, 2),
      (-2, -2)} : Set (ℤ × ℤ)) at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at hiC hjC hp
  have hneg : P.root i ≠ -P.root j :=
    b.root_ne_neg_of_ne i.property j.property (by simpa using hij)
  have hn22 : ¬ (b.cartanMatrix i j = -2 ∧
      b.cartanMatrix j i = -2) := by
    intro h
    exact hneg ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h)
  rcases (by aesop :
      (b.cartanMatrix i j = 0 ∧ b.cartanMatrix j i = 0) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
      (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1) ∨
      (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -3) ∨
      (b.cartanMatrix i j = -3 ∧ b.cartanMatrix j i = -1)) with
    h0 | h11 | h12 | h21 | h13 | h31
  · rw [hC, simpleReflection_mul_order_eq_two_of_cartan_zero
      b i j h0.1]
    norm_num
  · rw [hC, simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
      b i j h11.1 h11.2]
    norm_num
  · rw [hC, simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
      b i j h12.1 h12.2]
    norm_num
  · rw [hC, simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
      b i j h21.1 h21.2]
    norm_num
  · rw [hC, simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
      b i j h13.1 h13.2]
    norm_num
  · rw [hC, simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
      b i j h31.1 h31.2]
    norm_num

/-- Any two reduced simple-reflection words with the same Weyl-group product
are connected by Coxeter braid moves. -/
public theorem _root_.RootPairing.Base.reducedWords_reflTransGen_coxeterMove
    {I R M N : Type*} [Finite I] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (l m : List b.support)
    (hprod : b.wordProd l = b.wordProd m)
    (hl : l.length = b.wordLength (b.wordProd l))
    (hm : m.length = b.wordLength (b.wordProd m)) :
    Relation.ReflTransGen (CoxeterMove C) l m := by
  generalize hn : l.length = n
  induction n generalizing l m with
  | zero =>
      have hl0 : l = [] := List.length_eq_zero_iff.mp hn
      subst l
      have hm0 : m.length = 0 := by
        calc
          m.length = b.wordLength (b.wordProd m) := hm
          _ = b.wordLength (b.wordProd []) := by rw [hprod]
          _ = 0 := by simp
      have hmm : m = [] := List.length_eq_zero_iff.mp hm0
      subst m
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      have hlne : l ≠ [] := by
        intro h
        subst l
        simp at hn
      have hmlen : m.length = n + 1 := by
        calc
          m.length = b.wordLength (b.wordProd m) := hm
          _ = b.wordLength (b.wordProd l) := by rw [hprod]
          _ = l.length := hl.symm
          _ = n + 1 := hn
      have hmne : m ≠ [] := by
        intro h
        subst m
        simp at hmlen
      let i : b.support := l.getLast hlne
      let j : b.support := m.getLast hmne
      have hldecomp : l.dropLast ++ [i] = l :=
        List.dropLast_append_getLast hlne
      have hmdecomp : m.dropLast ++ [j] = m :=
        List.dropLast_append_getLast hmne
      have hllen : l.dropLast.length = n := by
        have := congrArg List.length hldecomp
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hmlen' : m.dropLast.length = n := by
        have := congrArg List.length hmdecomp
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hlred := reduced_dropLast b l hlne hl
      have hmred := reduced_dropLast b m hmne hm
      by_cases hij : i = j
      · have hji : j = i := hij.symm
        rw [hji] at hmdecomp
        have hlprod := wordProd_dropLast_eq_mul_last b l hlne
        have hmprod := wordProd_dropLast_eq_mul_last b m hmne
        change b.wordProd l.dropLast =
          b.wordProd l * b.simpleReflection i at hlprod
        change b.wordProd m.dropLast =
          b.wordProd m * b.simpleReflection j at hmprod
        rw [hji] at hmprod
        have hprefix : b.wordProd l.dropLast =
            b.wordProd m.dropLast := by
          rw [hlprod, hmprod, hprod]
        have hpath := ih l.dropLast m.dropLast hprefix hlred hmred hllen
        have happ := coxeterMove_reflTransGen_append_right C [i] hpath
        simpa only [hldecomp, hmdecomp] using happ
      · have hlprod := wordProd_dropLast_eq_mul_last b l hlne
        have hmprod := wordProd_dropLast_eq_mul_last b m hmne
        change b.wordProd l.dropLast =
          b.wordProd l * b.simpleReflection i at hlprod
        change b.wordProd m.dropLast =
          b.wordProd m * b.simpleReflection j at hmprod
        have hidesc : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) i) := by
          apply (wordLength_simpleReflection_iff_isPositive
            b (b.wordProd l) i).2.mp
          rw [← hlprod, ← hlred, ← hl]
          omega
        have hjdesc : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) j) := by
          apply (wordLength_simpleReflection_iff_isPositive
            b (b.wordProd l) j).2.mp
          rw [hprod, ← hmprod, ← hmred, ← hm]
          omega
        have hCpos : 0 < C j i :=
          coxeterMatrix_apply_pos_of_orders_of_ne
            b C hC j i (Ne.symm hij)
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hCpos.ne'
        let tailI : List b.support :=
          CoxeterSystem.alternatingWord i j k
        let tailJ : List b.support :=
          CoxeterSystem.alternatingWord j i k
        have hk' : C i j = k + 1 := (C.symmetric i j).trans hk
        have hqI : CoxeterSystem.braidWord C j i = tailI ++ [i] := by
          change CoxeterSystem.alternatingWord j i (C j i) =
            CoxeterSystem.alternatingWord i j k ++ [i]
          rw [hk, CoxeterSystem.alternatingWord_succ,
            List.concat_eq_append]
        have hqJ : CoxeterSystem.braidWord C i j = tailJ ++ [j] := by
          change CoxeterSystem.alternatingWord i j (C i j) =
            CoxeterSystem.alternatingWord j i k ++ [j]
          rw [hk', CoxeterSystem.alternatingWord_succ,
            List.concat_eq_append]
        have hdrop :=
          b.wordLength_mul_braidWord_add_eq_of_two_descents
            C hC (b.wordProd l) j i hjdesc hidesc
        obtain ⟨p, hplen, hpprod⟩ :=
          b.wordLength_spec
            (b.wordProd l *
              b.wordProd (CoxeterSystem.braidWord C j i))
        have hsqI := b.wordProd_braidWord_mul_self_of_orders C hC j i
        have hsqJ := b.wordProd_braidWord_mul_self_of_orders C hC i j
        have hbraid := b.wordProd_braidWord_eq_of_orders C hC j i
        have hfullIprod : b.wordProd
            (p ++ CoxeterSystem.braidWord C j i) = b.wordProd l := by
          rw [b.wordProd_append, hpprod, mul_assoc, hsqI, mul_one]
        have hfullJprod : b.wordProd
            (p ++ CoxeterSystem.braidWord C i j) = b.wordProd l := by
          rw [b.wordProd_append, hpprod, hbraid, mul_assoc, hsqJ,
            mul_one]
        have hfullIlen :
            (p ++ CoxeterSystem.braidWord C j i).length =
              b.wordLength (b.wordProd l) := by
          simp only [List.length_append,
            CoxeterSystem.length_alternatingWord]
          rw [hplen]
          exact hdrop
        have hfullJlen :
            (p ++ CoxeterSystem.braidWord C i j).length =
              b.wordLength (b.wordProd l) := by
          simp only [List.length_append,
            CoxeterSystem.length_alternatingWord]
          rw [hplen, C.symmetric i j]
          exact hdrop
        have hfullIred :
            (p ++ CoxeterSystem.braidWord C j i).length =
              b.wordLength
                (b.wordProd (p ++ CoxeterSystem.braidWord C j i)) := by
          rw [hfullIprod]
          exact hfullIlen
        have hfullJred :
            (p ++ CoxeterSystem.braidWord C i j).length =
              b.wordLength
                (b.wordProd (p ++ CoxeterSystem.braidWord C i j)) := by
          rw [hfullJprod]
          exact hfullJlen
        have hfullIdecomp : (p ++ tailI) ++ [i] =
            p ++ CoxeterSystem.braidWord C j i := by
          rw [hqI]
          simp only [List.append_assoc]
        have hfullJdecomp : (p ++ tailJ) ++ [j] =
            p ++ CoxeterSystem.braidWord C i j := by
          rw [hqJ]
          simp only [List.append_assoc]
        have hprefixIred : (p ++ tailI).length =
            b.wordLength (b.wordProd (p ++ tailI)) := by
          apply reduced_prefix_of_append_singleton b (p ++ tailI) i
          rw [hfullIdecomp]
          exact hfullIred
        have hprefixJred : (p ++ tailJ).length =
            b.wordLength (b.wordProd (p ++ tailJ)) := by
          apply reduced_prefix_of_append_singleton b (p ++ tailJ) j
          rw [hfullJdecomp]
          exact hfullJred
        have hprefixIlen : (p ++ tailI).length = n := by
          have hfulln :
              (p ++ CoxeterSystem.braidWord C j i).length = n + 1 := by
            rw [hfullIlen, ← hl, hn]
          exact Nat.add_right_cancel (by
            calc
              (p ++ tailI).length + 1 =
                  ((p ++ tailI) ++ [i]).length := by simp [Nat.add_assoc]
              _ = (p ++ CoxeterSystem.braidWord C j i).length :=
                congrArg List.length hfullIdecomp
              _ = n + 1 := hfulln)
        have hprefixJlen : (p ++ tailJ).length = n := by
          have hfulln :
              (p ++ CoxeterSystem.braidWord C i j).length = n + 1 := by
            rw [hfullJlen, ← hl, hn]
          exact Nat.add_right_cancel (by
            calc
              (p ++ tailJ).length + 1 =
                  ((p ++ tailJ) ++ [j]).length := by simp [Nat.add_assoc]
              _ = (p ++ CoxeterSystem.braidWord C i j).length :=
                congrArg List.length hfullJdecomp
              _ = n + 1 := hfulln)
        have hprefixIprod : b.wordProd l.dropLast =
            b.wordProd (p ++ tailI) := by
          rw [hlprod,
            wordProd_prefix_eq_append_singleton_mul b (p ++ tailI) i,
            hfullIdecomp, hfullIprod]
        have hprefixJprod : b.wordProd (p ++ tailJ) =
            b.wordProd m.dropLast := by
          rw [wordProd_prefix_eq_append_singleton_mul b (p ++ tailJ) j,
            hfullJdecomp, hfullJprod, hmprod, hprod]
        have hleftPrefix := ih l.dropLast (p ++ tailI)
          hprefixIprod hlred hprefixIred hllen
        have hleft := coxeterMove_reflTransGen_append_right
          C [i] hleftPrefix
        rw [hldecomp, hfullIdecomp] at hleft
        have hrightPrefix := ih (p ++ tailJ) m.dropLast
          hprefixJprod hprefixJred hmred hprefixJlen
        have hright := coxeterMove_reflTransGen_append_right
          C [j] hrightPrefix
        rw [hfullJdecomp, hmdecomp] at hright
        have hmiddleMove : CoxeterMove C
            (p ++ CoxeterSystem.braidWord C j i)
            (p ++ CoxeterSystem.braidWord C i j) := by
          simpa using coxeterMove_braid C p [] j i
        have hmiddle := Relation.ReflTransGen.single hmiddleMove
        exact hleft.trans (hmiddle.trans hright)

end Theory.AlgebraicGroup
