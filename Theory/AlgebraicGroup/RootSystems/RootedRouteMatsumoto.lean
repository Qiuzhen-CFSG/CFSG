module

public import Theory.AlgebraicGroup.RootSystems.Deletion

/-!
# Rooted Matsumoto connectivity

This module proves connectivity for marked simple-reflection words with the
same transported root.  The repaired relation has four generators: ordinary
Coxeter moves at a fixed source, terminal orthogonal deletion, terminal `A₂`
source exchange, and deletion of an arbitrary terminal word fixing the marked
simple root.  The last generator is essential: in type `B₂`, the nontrivial
word `[j, i, j]` fixes `i` but cannot be removed by the first three moves.

Endpoints are expressed through the Weyl permutation
`P.weylGroupToPerm (b.wordProd word)`, so this result stays below the integral
operator layers.  The proof first reduces equal Weyl-group products using
deletion and ordinary Matsumoto connectivity.  A `ZMod 2` parity invariant for
each component of the graph of `A₂` simple pairs shows that conjugate simple
reflections have markers in the same `A₂` component.  Terminal `A₂` exchanges
align those markers; after that, an arbitrary rooted-stabilizer deletion
completes the path.  The standard `B₂` counterexample to the unrepaired
relation is checked separately in the task's scratch directory.

The Coxeter and deletion ingredients are developed in `Coxeter.lean`,
`Matsumoto.lean`, `Deletion.lean`, and `Weyl.lean`.  Integral operator consumers
can rewrite their `reflectionWord` endpoints with
`reflectionWord_eq_weylGroupToPerm` before applying the completeness theorem.
-/

namespace Theory.AlgebraicGroup
set_option linter.unusedSectionVars false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- A marked route move.  Besides fixed-source Coxeter moves and the two
terminal rank-two moves, its last branch deletes any terminal word fixing the
marked simple root. -/
@[expose] public def RepairedRootedRouteMove (C : CoxeterMatrix b.support)
    (source result : List b.support × b.support) : Prop :=
  (source.2 = result.2 ∧ CoxeterMove C source.1 result.1) ∨
    (∃ (left : List b.support) (i j : b.support),
      b.cartanMatrix i j = 0 ∧
        source = (left ++ [j], i) ∧ result = (left, i)) ∨
    (∃ (left : List b.support) (i j : b.support),
      i ≠ j ∧ b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1 ∧
        source = (left ++ [i], j) ∧ result = (left ++ [j], i)) ∨
    (∃ (left tail : List b.support) (i : b.support),
      source = (left ++ tail, i) ∧ result = (left, i) ∧
        P.weylGroupToPerm (b.wordProd tail) (i : ι) = (i : ι))

private lemma wordProd_eq_of_coxeterMove
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support} (hmove : CoxeterMove C source result) :
    b.wordProd source = b.wordProd result := by
  rcases hmove with hcancel | hbraid
  · rcases hcancel with ⟨left, right, i, rfl, rfl⟩
    simp only [b.wordProd_append, b.wordProd_cons, b.wordProd_nil, mul_one]
    rw [mul_assoc, b.simpleReflection_mul_self, one_mul]
  · rcases hbraid with ⟨left, right, i, j, rfl, rfl⟩
    simp only [b.wordProd_append]
    rw [b.wordProd_braidWord_eq_of_orders C hC i j]

private lemma wordEndpoint_append (left right : List b.support) (k : ι) :
    P.weylGroupToPerm (b.wordProd (left ++ right)) k =
      P.weylGroupToPerm (b.wordProd left)
        (P.weylGroupToPerm (b.wordProd right) k) := by
  rw [b.wordProd_append]
  rfl

private lemma root_wordEndpoint (word : List b.support) (i : ι) :
    P.root (P.weylGroupToPerm (b.wordProd word) i) =
      b.wordProd word • P.root i :=
  (P.weylGroup_apply_root (b.wordProd word) i).symm

private lemma reflectionPerm_eq_of_orthogonal
    (i j : b.support) (hij : b.cartanMatrix i j = 0) :
    P.reflectionPerm j i = i := by
  apply P.root.injective
  change P.pairingIn ℤ (i : ι) (j : ι) = 0 at hij
  rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hij]
  simp

private lemma reflectionPerm_eq_of_a2
    (i j : b.support) (hij : b.cartanMatrix i j = -1)
    (hji : b.cartanMatrix j i = -1) :
    P.reflectionPerm i j = P.reflectionPerm j i := by
  apply P.root.injective
  change P.pairingIn ℤ (i : ι) (j : ι) = -1 at hij
  change P.pairingIn ℤ (j : ι) (i : ι) = -1 at hji
  rw [P.root_reflectionPerm, P.root_reflectionPerm,
    P.reflection_apply_root' ℤ, P.reflection_apply_root' ℤ, hij, hji]
  module

/-- Every repaired generating move preserves the marked transported root. -/
public theorem repairedRootedRouteMove_endpoint
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support × b.support}
    (hmove : RepairedRootedRouteMove (P := P) (b := b) C source result) :
    P.weylGroupToPerm (b.wordProd source.1) (source.2 : ι) =
      P.weylGroupToPerm (b.wordProd result.1) (result.2 : ι) := by
  rcases hmove with hcox | hterminal
  · rw [wordProd_eq_of_coxeterMove C hC hcox.2, hcox.1]
  · rcases hterminal with horth | hrest
    · rcases horth with ⟨left, i, j, hij, rfl, rfl⟩
      rw [wordEndpoint_append]
      change P.weylGroupToPerm (b.wordProd left) (P.reflectionPerm j i) =
        P.weylGroupToPerm (b.wordProd left) i
      rw [reflectionPerm_eq_of_orthogonal i j hij]
    · rcases hrest with ha2 | hstab
      · rcases ha2 with ⟨left, i, j, _hij, hij, hji, rfl, rfl⟩
        rw [wordEndpoint_append, wordEndpoint_append]
        change P.weylGroupToPerm (b.wordProd left) (P.reflectionPerm i j) =
          P.weylGroupToPerm (b.wordProd left) (P.reflectionPerm j i)
        rw [reflectionPerm_eq_of_a2 i j hij hji]
      · rcases hstab with ⟨left, tail, i, rfl, rfl, hfix⟩
        rw [wordEndpoint_append, hfix]

/-- The equivalence closure of repaired moves preserves the transported-root
endpoint. -/
public theorem repairedRootedRouteMove_eqv_endpoint
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support × b.support}
    (hpath : Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
      source result) :
    P.weylGroupToPerm (b.wordProd source.1) (source.2 : ι) =
      P.weylGroupToPerm (b.wordProd result.1) (result.2 : ι) := by
  induction hpath with
  | rel source result hmove =>
      exact repairedRootedRouteMove_endpoint C hC hmove
  | refl source => rfl
  | symm source result h ih => exact ih.symm
  | trans source middle result h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private def A2Linked (i j : b.support) : Prop :=
  i ≠ j ∧ b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1

private lemma a2Linked_symm {i j : b.support}
    (h : A2Linked (b := b) i j) : A2Linked (b := b) j i :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

private noncomputable def markerValue (root j : b.support) : ZMod 2 := by
  classical
  exact if Relation.EqvGen (A2Linked (b := b)) root j then 1 else 0

private noncomputable def wordParity (root : b.support)
    (word : List b.support) : ZMod 2 :=
  (word.map (markerValue (b := b) root)).sum

private lemma markerValue_self (root : b.support) :
    markerValue (b := b) root root = 1 := by
  classical
  rw [markerValue, if_pos (Relation.EqvGen.refl root)]

private lemma markerValue_eq_of_a2 (root : b.support) {i j : b.support}
    (h : A2Linked (b := b) i j) :
    markerValue (b := b) root i = markerValue (b := b) root j := by
  classical
  simp only [markerValue]
  congr 1
  apply propext
  exact ⟨fun hi => Relation.EqvGen.trans root i j hi
      (Relation.EqvGen.rel i j h),
    fun hj => Relation.EqvGen.trans root j i hj
      (Relation.EqvGen.rel j i (a2Linked_symm h))⟩

private lemma wordParity_append (root : b.support)
    (left right : List b.support) :
    wordParity (b := b) root (left ++ right) =
      wordParity root left + wordParity root right := by
  simp [wordParity]

private lemma wordParity_reverse (root : b.support) (word : List b.support) :
    wordParity (b := b) root word.reverse = wordParity root word := by
  simp [wordParity]

private lemma coxeterMatrix_cases
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i j : b.support) :
    i = j ∨ C i j = 2 ∨
      (C i j = 3 ∧ A2Linked (b := b) i j) ∨
      C i j = 4 ∨ C i j = 6 := by
  by_cases hij : i = j
  · exact Or.inl hij
  right
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
  · left
    rw [hC, simpleReflection_mul_order_eq_two_of_cartan_zero
      b i j h0.1]
  · exact Or.inr (Or.inl ⟨by
      rw [hC, simpleReflection_mul_order_eq_three_of_cartan_neg_one_neg_one
        b i j h11.1 h11.2], ⟨hij, h11⟩⟩)
  · exact Or.inr (Or.inr (Or.inl (by
      rw [hC, simpleReflection_mul_order_eq_four_of_cartan_neg_one_neg_two
        b i j h12.1 h12.2])))
  · exact Or.inr (Or.inr (Or.inl (by
      rw [hC, simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
        b i j h21.1 h21.2])))
  · exact Or.inr (Or.inr (Or.inr (by
      rw [hC, simpleReflection_mul_order_eq_six_of_cartan_neg_one_neg_three
        b i j h13.1 h13.2])))
  · exact Or.inr (Or.inr (Or.inr (by
      rw [hC, simpleReflection_mul_order_eq_six_of_cartan_neg_three_neg_one
        b i j h31.1 h31.2])))

private lemma wordParity_coxeterMove
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (root : b.support) {source result : List b.support}
    (hmove : CoxeterMove C source result) :
    wordParity (b := b) root source = wordParity root result := by
  rcases hmove with hcancel | hbraid
  · rcases hcancel with ⟨left, right, i, rfl, rfl⟩
    simp only [wordParity_append]
    simp only [wordParity, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [CharTwo.add_self_eq_zero, add_zero]
  · rcases hbraid with ⟨left, right, i, j, rfl, rfl⟩
    simp only [wordParity_append]
    suffices wordParity (b := b) root (CoxeterSystem.braidWord C i j) =
        wordParity root (CoxeterSystem.braidWord C j i) by rw [this]
    change wordParity (b := b) root
        (CoxeterSystem.alternatingWord i j (C i j)) =
      wordParity root (CoxeterSystem.alternatingWord j i (C j i))
    rcases coxeterMatrix_cases C hC i j with hij | h2 | h3 | h4 | h6
    · subst j
      rfl
    · rw [h2, C.symmetric j i, h2]
      simp [CoxeterSystem.alternatingWord, wordParity, add_comm]
    · rcases h3 with ⟨hC3, ha2⟩
      have hv := markerValue_eq_of_a2 (b := b) root ha2
      rw [hC3, C.symmetric j i, hC3]
      simp [CoxeterSystem.alternatingWord, wordParity, hv, add_comm]
    · rw [h4, C.symmetric j i, h4]
      simp [CoxeterSystem.alternatingWord, wordParity, add_comm, add_left_comm]
    · rw [h6, C.symmetric j i, h6]
      simp [CoxeterSystem.alternatingWord, wordParity, add_comm, add_left_comm]

private lemma wordParity_eq_of_coxeterEqv
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (root : b.support) {source result : List b.support}
    (hpath : Relation.EqvGen (CoxeterMove C) source result) :
    wordParity (b := b) root source = wordParity root result := by
  induction hpath with
  | rel source result hmove => exact wordParity_coxeterMove C hC root hmove
  | refl source => rfl
  | symm source result h ih => exact ih.symm
  | trans source middle result h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma coxeterEqv_of_wordProd_eq
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support}
    (hprod : b.wordProd source = b.wordProd result) :
    Relation.EqvGen (CoxeterMove C) source result := by
  obtain ⟨source', hsProd, hsRed, hsPath⟩ :=
    b.exists_reducedWord_reflTransGen_coxeterMove C hC source
  obtain ⟨result', hrProd, hrRed, hrPath⟩ :=
    b.exists_reducedWord_reflTransGen_coxeterMove C hC result
  have hsrProd : b.wordProd source' = b.wordProd result' :=
    hsProd.trans (hprod.trans hrProd.symm)
  have hmiddle := b.reducedWords_reflTransGen_coxeterMove
    C hC source' result' hsrProd hsRed hrRed
  have hsEqv : Relation.EqvGen (CoxeterMove C) source source' :=
    Relation.EqvGen.reflTransGen_le_eqvGen (CoxeterMove C) source source' hsPath
  have hmEqv : Relation.EqvGen (CoxeterMove C) source' result' :=
    Relation.EqvGen.reflTransGen_le_eqvGen (CoxeterMove C) source' result' hmiddle
  have hrEqv : Relation.EqvGen (CoxeterMove C) result result' :=
    Relation.EqvGen.reflTransGen_le_eqvGen (CoxeterMove C) result result' hrPath
  exact Relation.EqvGen.trans source source' result hsEqv
    (Relation.EqvGen.trans source' result' result hmEqv
      (Relation.EqvGen.symm result result' hrEqv))

private lemma wordParity_eq_of_wordProd_eq
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (root : b.support) {source result : List b.support}
    (hprod : b.wordProd source = b.wordProd result) :
    wordParity (b := b) root source = wordParity root result :=
  wordParity_eq_of_coxeterEqv C hC root
    (coxeterEqv_of_wordProd_eq C hC hprod)

private lemma wordProd_reverse (word : List b.support) :
    b.wordProd word.reverse = (b.wordProd word)⁻¹ := by
  induction word with
  | nil => simp
  | cons i word ih =>
      simp only [List.reverse_cons, b.wordProd_append, b.wordProd_cons, ih]
      simp

private lemma wordProd_conjugate_simpleReflection
    (word : List b.support) (i : b.support) :
    b.wordProd word * b.simpleReflection i * (b.wordProd word)⁻¹ =
      RootPairing.weylGroup.ofIdx P
        (P.weylGroupToPerm (b.wordProd word) (i : ι)) := by
  change b.wordProd word * RootPairing.weylGroup.ofIdx P (i : ι) *
      (b.wordProd word)⁻¹ = _
  rw [b.wordProd_mul_ofIdx]
  group

private lemma repairedEqv_of_coxeterEqv
    (C : CoxeterMatrix b.support) (i : b.support)
    {source result : List b.support}
    (hpath : Relation.EqvGen (CoxeterMove C) source result) :
    Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
      (source, i) (result, i) := by
  induction hpath with
  | rel source result hmove =>
      exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, hmove⟩)
  | refl source => exact Relation.EqvGen.refl _
  | symm source result hmove ih =>
      exact Relation.EqvGen.symm (source, i) (result, i) ih
  | trans source middle result h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans (source, i) (middle, i) (result, i) ih₁ ih₂

private lemma repairedEqv_of_wordProd_eq
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    (i : b.support) {source result : List b.support}
    (hprod : b.wordProd source = b.wordProd result) :
    Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
      (source, i) (result, i) :=
  repairedEqv_of_coxeterEqv C i (coxeterEqv_of_wordProd_eq C hC hprod)

private lemma exists_repairedEqv_change_marker_of_a2
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {i j : b.support} (hij : A2Linked (b := b) i j)
    (word : List b.support) :
    ∃ result : List b.support,
      Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
        (word, i) (result, j) := by
  obtain ⟨left, hleft⟩ :=
    b.exists_wordProd_eq (b.wordProd word * b.simpleReflection j)
  have hprod : b.wordProd word = b.wordProd (left ++ [j]) := by
    rw [b.wordProd_append, b.wordProd_cons, b.wordProd_nil, mul_one, hleft]
    rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
  have hfixed := repairedEqv_of_wordProd_eq C hC i hprod
  have hchange : RepairedRootedRouteMove (P := P) (b := b) C
      ((left ++ [j], i) : List b.support × b.support) (left ++ [i], j) := by
    exact Or.inr (Or.inr (Or.inl
      ⟨left, j, i, hij.1.symm, hij.2.2, hij.2.1, rfl, rfl⟩))
  refine ⟨left ++ [i], ?_⟩
  exact Relation.EqvGen.trans (word, i) (left ++ [j], i) (left ++ [i], j)
    hfixed (Relation.EqvGen.rel _ _ hchange)

private lemma exists_repairedEqv_change_marker
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {i j : b.support} (hmarkers : Relation.EqvGen (A2Linked (b := b)) i j)
    (word : List b.support) :
    ∃ result : List b.support,
      Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
        (word, i) (result, j) := by
  let _ : Std.Symm (A2Linked (b := b)) := ⟨fun _ _ h => a2Linked_symm h⟩
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen] at hmarkers
  induction hmarkers using Relation.ReflTransGen.trans_induction_on generalizing word with
  | refl i => exact ⟨word, Relation.EqvGen.refl (word, i)⟩
  | single hij => exact exists_repairedEqv_change_marker_of_a2 C hC hij word
  | trans hij hjk ihij ihjk =>
      obtain ⟨middle, hfirst⟩ := ihij word
      obtain ⟨result, hsecond⟩ := ihjk middle
      exact ⟨result, Relation.EqvGen.trans _ _ _ hfirst hsecond⟩

private lemma a2Connected_of_endpoint_eq
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support} {i j : b.support}
    (hendpoint : P.weylGroupToPerm (b.wordProd source) (i : ι) =
      P.weylGroupToPerm (b.wordProd result) (j : ι)) :
    Relation.EqvGen (A2Linked (b := b)) i j := by
  classical
  let conjugator := result.reverse ++ source
  have hconjugate :
      b.wordProd source * b.simpleReflection i * (b.wordProd source)⁻¹ =
        b.wordProd result * b.simpleReflection j * (b.wordProd result)⁻¹ :=
    (wordProd_conjugate_simpleReflection source i).trans
      ((congrArg (RootPairing.weylGroup.ofIdx P) hendpoint).trans
        (wordProd_conjugate_simpleReflection result j).symm)
  have hconjugator : b.wordProd conjugator =
      (b.wordProd result)⁻¹ * b.wordProd source := by
    simp only [conjugator, b.wordProd_append, wordProd_reverse]
  have hprod :
      b.wordProd (conjugator ++ [i] ++ conjugator.reverse) =
        b.wordProd [j] := by
    rw [b.wordProd_append, b.wordProd_append, wordProd_reverse,
      b.wordProd_cons, b.wordProd_nil, mul_one, hconjugator]
    calc
      (((b.wordProd result)⁻¹ * b.wordProd source) * b.simpleReflection i) *
          ((b.wordProd result)⁻¹ * b.wordProd source)⁻¹ =
        (b.wordProd result)⁻¹ *
          (b.wordProd source * b.simpleReflection i * (b.wordProd source)⁻¹) *
            b.wordProd result := by group
      _ = (b.wordProd result)⁻¹ *
          (b.wordProd result * b.simpleReflection j * (b.wordProd result)⁻¹) *
            b.wordProd result := by rw [hconjugate]
      _ = b.simpleReflection j := by group
  have hparity := wordParity_eq_of_wordProd_eq C hC i hprod
  have hleft : wordParity (b := b) i
      (conjugator ++ [i] ++ conjugator.reverse) = 1 := by
    rw [wordParity_append, wordParity_append, wordParity_reverse]
    simp [wordParity, markerValue_self, add_comm, add_left_comm]
    exact CharTwo.add_self_eq_zero _
  by_contra hnot
  have hright : wordParity (b := b) i [j] = 0 := by
    simp [wordParity, markerValue, hnot]
  have hone : (1 : ZMod 2) = 0 := hleft.symm.trans (hparity.trans hright)
  exact one_ne_zero hone

private lemma repairedEqv_same_marker_of_endpoint_eq
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support} (i : b.support)
    (hendpoint : P.weylGroupToPerm (b.wordProd source) (i : ι) =
      P.weylGroupToPerm (b.wordProd result) (i : ι)) :
    Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
      (source, i) (result, i) := by
  let tail := result.reverse ++ source
  have hroot : b.wordProd source • P.root (i : ι) =
      b.wordProd result • P.root (i : ι) := by
    rw [← root_wordEndpoint source (i : ι),
      ← root_wordEndpoint result (i : ι), hendpoint]
  have hfix : P.weylGroupToPerm (b.wordProd tail) (i : ι) = (i : ι) := by
    apply P.root.injective
    dsimp only [tail]
    rw [root_wordEndpoint, b.wordProd_append, wordProd_reverse,
      mul_smul, hroot, inv_smul_smul]
  have hprod : b.wordProd source = b.wordProd (result ++ tail) := by
    dsimp only [tail]
    rw [b.wordProd_append, b.wordProd_append, wordProd_reverse]
    group
  have hfixed := repairedEqv_of_wordProd_eq C hC i hprod
  have hdelete : RepairedRootedRouteMove (P := P) (b := b) C
      ((result ++ tail, i) : List b.support × b.support) (result, i) := by
    exact Or.inr (Or.inr (Or.inr ⟨result, tail, i, rfl, rfl, hfix⟩))
  exact Relation.EqvGen.trans (source, i) (result ++ tail, i) (result, i)
    hfixed (Relation.EqvGen.rel _ _ hdelete)

/-- Equal transported-root endpoints are connected by repaired rooted route
moves. -/
public theorem repairedRootedRouteMove_complete
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support × b.support}
    (hendpoint : P.weylGroupToPerm (b.wordProd source.1) (source.2 : ι) =
      P.weylGroupToPerm (b.wordProd result.1) (result.2 : ι)) :
    Relation.EqvGen (RepairedRootedRouteMove (P := P) (b := b) C)
      source result := by
  have hmarkers := a2Connected_of_endpoint_eq C hC hendpoint
  obtain ⟨middle, hchange⟩ :=
    exists_repairedEqv_change_marker C hC hmarkers source.1
  have hchangeEndpoint := repairedRootedRouteMove_eqv_endpoint C hC hchange
  have hmiddleEndpoint :
      P.weylGroupToPerm (b.wordProd middle) (result.2 : ι) =
        P.weylGroupToPerm (b.wordProd result.1) (result.2 : ι) :=
    hchangeEndpoint.symm.trans hendpoint
  have hfinish := repairedEqv_same_marker_of_endpoint_eq C hC result.2 hmiddleEndpoint
  exact Relation.EqvGen.trans source (middle, result.2) result hchange hfinish

end
end Theory.AlgebraicGroup
