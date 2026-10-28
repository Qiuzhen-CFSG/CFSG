module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.NonabelianRadicals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# The exact five-root radical and its three middle roots

For rotation order six and distinct endpoints i,j, the radical V_j is
U_i U_j^{s_i} U_i^{s_j s_i} U_j^{s_i s_j} U_i^{s_j}, in that order.
The three middle factors form exactly V_j intersect V_i intersect V_i^{s_j}.
They are preserved by every lift of s_j in N. The proof uses the longest
Weyl word and the previously established unique ordered coordinates;
removing the two outside factors uses the disjoint simple root complements.

All subgroups lie in the same finite quotient and all exponent words denote
right conjugation. These are the literal products in Fong--Seitz I (3G),
printed pp.14--16, and (6E), printed p.44. No parameter, local perfectness,
commutator equality or representation hypothesis is used here.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem sinv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem longest_six (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
  have h0 := alternatingWord_longest Q false
  have h1 := alternatingWord_longest Q true
  rw [hm] at h0 h1
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
  · exact (hij rfl).elim

private theorem longest_comm (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.simple i * longest Q = longest Q * Q.simple i := by
  conv_lhs => rw [longest_six Q hm i j hij]
  conv_rhs => rw [longest_six Q hm j i hij.symm]
  simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i), ssq,
    one_mul, mul_one]

private theorem rootAt_stabilizer (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (longest Q*Q.simple i) = simpleRoot Q split i := by
  have he : (longest Q*Q.simple i)*(longest Q*Q.simple i) = 1 := by
    rw [mul_assoc, ← mul_assoc (Q.simple i), longest_comm Q hm i j hij,
      ← mul_assoc, ← mul_assoc, longest_mul_self, one_mul, ssq]
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest Q*Q.simple i))
    (representative (longest Q*Q.simple i) : X ⧸ Q.D) = _
  rw [rightConjugate_inf, ← unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _), he,
    unipotentConjugate_one, inf_comm]
  rfl

private theorem rootAt_stabilizer_mul (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (w : Weyl Q) :
    rootAt Q split i ((longest Q*Q.simple i)*w) = rootAt Q split i w := by
  rw [← rootAt_right Q split i _ w (representative w) (representative_spec _),
    rootAt_stabilizer Q split hm i j hij]
  rfl

private theorem rootAt_four (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j) := by
  have he : (longest Q*Q.simple i)*Q.simple j =
      Q.simple j*Q.simple i*Q.simple j*Q.simple i := by
    rw [longest_six Q hm j i hij.symm]
    simp only [mul_assoc, ssq, mul_one]
  rw [← he, rootAt_stabilizer_mul Q split hm i j hij]

private theorem rootAt_three (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split j (Q.simple i*Q.simple j) := by
  have he : (longest Q*Q.simple j)*(Q.simple i*Q.simple j) =
      Q.simple i*Q.simple j*Q.simple i := by
    rw [longest_six Q hm i j hij]
    simp only [mul_assoc, ssq, one_mul, ← mul_assoc (Q.simple i) (Q.simple i), mul_one]
  rw [← he, rootAt_stabilizer_mul Q split hm j i hij.symm]

private theorem rootAt_rep (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl
private theorem rootAt_right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) :=
  rootAt_right Q split i v w _ (representative_spec _)

private theorem ordered_five (hm : rotationOrder Q = 6) (b : Bool) :
    let i : Fin 2 := if b then 1 else 0
    let j : Fin 2 := if b then 0 else 1
    orderedRoots Q split b 5 = [simpleRoot Q split i,
      rootAt Q split j (Q.simple i), rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split j (Q.simple i*Q.simple j), rootAt Q split i (Q.simple j)] := by
  cases b <;>
    simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, List.map_cons, List.map_nil, rootAt_rep, rootAt_right_rep]
  · rw [rootAt_three Q split hm 0 1 (by decide), rootAt_four Q split hm 0 1 (by decide)]
  · rw [rootAt_three Q split hm 1 0 (by decide), rootAt_four Q split hm 1 0 (by decide)]

private theorem five_intersection (hm : rotationOrder Q = 6) (b : Bool) :
    rootIntersection split (longest Q) (alternatingWord Q b 5)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
  have he : (alternatingWord Q b 5)⁻¹ = longest Q*Q.simple (if b then 0 else 1) := by
    cases b
    · rw [longest_six Q hm 0 1 (by decide)]
      simp only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, mul_inv_rev, sinv, mul_one, mul_assoc, ssq]
    · rw [longest_six Q hm 1 0 (by decide)]
      simp only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, mul_inv_rev, sinv, mul_one, mul_assoc, ssq]
  rw [he, rootIntersection_complement]
  rfl

/-- The five source roots in the radical, in circular order. -/
theorem radical_five_product (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    (simpleRemainder Q split j : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
  have hh (b : Bool) := orderedRoots_product Q split b 5 (by omega)
  simp only [ordered_five Q split hm, five_intersection Q split hm] at hh
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := (hh false).symm
    change (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) =
      (simpleRoot Q split 0 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) * 1)))) at ht
    simpa only [mul_one, mul_assoc] using ht
  · have ht := (hh true).symm
    change (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) =
      (simpleRoot Q split 1 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) * 1)))) at ht
    simpa only [mul_one, mul_assoc] using ht
  · exact (hij rfl).elim

private theorem rootAt_remainder_conjugate (i : Fin 2) (w : Weyl Q) (j : Fin 2)
    (h : rootAt Q split i (w*Q.simple j) ≤ simpleRemainder Q split j) :
    rootAt Q split i w ≤ simpleRemainder Q split j := by
  let n := representative (Q.simple j)
  have hV : rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D) =
      simpleRemainder Q split j := by
    rw [simpleRemainder, rightConjugate_inf,
      ← unipotentConjugate_eq split _ n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _), ssq,
      unipotentConjugate_one, inf_comm]
  have hc := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) h
  change rightConjugate (rootAt Q split i (w*Q.simple j)) (n : X ⧸ Q.D) ≤
    rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D) at hc
  rwa [rootAt_right_rep, mul_assoc, ssq, mul_one, hV] at hc


private theorem lengths_three (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega))
    (wordLength_alternatingWord Q b (n := 3) (by omega)))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

private theorem terminal_le_other_remainder (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i := by
  have hi := lengths_three Q hm i j hij
  have hj := lengths_three Q hm j i hij.symm
  apply rootAt_le_remainder Q split i i (Q.simple j)
  · rw [sinv, hj.1, hj.2.1]
  · rw [sinv, hi.2.1, hi.2.2]

/-- The three middle roots of the source radical. -/
@[expose] def middleRoots (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  rootAt Q split j (Q.simple i) ⊔ rootAt Q split i (Q.simple j*Q.simple i) ⊔
    rootAt Q split j (Q.simple i*Q.simple j)

private theorem first_le_middle (i j : Fin 2) :
    rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j :=
  le_sup_left.trans le_sup_left
private theorem second_le_middle (i j : Fin 2) :
    rootAt Q split i (Q.simple j*Q.simple i) ≤ middleRoots Q split i j :=
  le_sup_right.trans le_sup_left
private theorem third_le_middle (i j : Fin 2) :
    rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j := le_sup_right

theorem middleRoots_le_other_remainder (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    middleRoots Q split i j ≤ simpleRemainder Q split i := by
  obtain ⟨hB,hD⟩ := exchanged_roots_le_remainder Q split hm j i hij.symm
  have hC : rootAt Q split i (Q.simple j*Q.simple i) ≤ simpleRemainder Q split i := by
    apply rootAt_remainder_conjugate Q split i _ i
    rw [mul_assoc, ssq, mul_one]
    exact terminal_le_other_remainder Q split hm i j hij
  exact sup_le (sup_le hB hC) hD

theorem middleRoots_le_remainder (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    middleRoots Q split i j ≤ simpleRemainder Q split j := by
  have hB := terminal_le_other_remainder Q split hm j i hij.symm
  have hC := (exchanged_roots_le_remainder Q split hm i j hij).2
  have hD : rootAt Q split j (Q.simple i*Q.simple j) ≤ simpleRemainder Q split j := by
    apply rootAt_remainder_conjugate Q split j _ j
    rw [mul_assoc, ssq, mul_one]
    exact hB
  exact sup_le (sup_le hB hC) hD

theorem middleRoots_conjugate (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple j) :
    rightConjugate (middleRoots Q split i j) (n : X ⧸ Q.D) =
      middleRoots Q split i j := by
  unfold middleRoots rightConjugate

  rw [← comap_sup_eq _ _ _ (MulAut.conj (n : X ⧸ Q.D)).surjective,
    ← comap_sup_eq _ _ _ (MulAut.conj (n : X ⧸ Q.D)).surjective]
  change rightConjugate (rootAt Q split j (Q.simple i)) (n : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i)) (n : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split j (Q.simple i*Q.simple j)) (n : X ⧸ Q.D) = _
  rw [rootAt_right Q split _ _ _ n hn, rootAt_right Q split _ _ _ n hn,
    rootAt_right Q split _ _ _ n hn, rootAt_three Q split hm j i hij.symm,
    mul_assoc, ssq, mul_one]
  simp only [sup_comm, sup_assoc]

theorem middleRoots_eq_intersection (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple j) :
    middleRoots Q split i j = simpleRemainder Q split j ⊓ simpleRemainder Q split i ⊓
      rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D) := by
  have hMV := middleRoots_le_other_remainder Q split hm i j hij
  have hMC : middleRoots Q split i j ≤
      rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D) := by
    rw [← middleRoots_conjugate Q split hm i j hij n hn]
    exact comap_mono hMV
  apply le_antisymm
  · exact le_inf (le_inf (middleRoots_le_remainder Q split hm i j hij) hMV) hMC
  · intro x hx
    have hxV : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx.1.1
    rw [radical_five_product Q split hm i j hij] at hxV
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hxV
    have hmemb : b ∈ middleRoots Q split i j := first_le_middle Q split i j hb
    have hmemc : c ∈ middleRoots Q split i j := second_le_middle Q split i j hc
    have hmemd : d ∈ middleRoots Q split i j := third_le_middle Q split i j hd
    have hbcde : b*c*d*e ∈ simpleRemainder Q split i :=
      mul_mem (hMV (mul_mem (mul_mem hmemb hmemc) hmemd))
        (terminal_le_other_remainder Q split hm i j hij he)
    have haV : a ∈ simpleRemainder Q split i := by
      have ht := (simpleRemainder Q split i).mul_mem hx.1.2 (inv_mem hbcde)
      simpa only [mul_assoc, mul_inv_rev, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ht
    have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
    subst a
    simp only [one_mul] at hx
    have heC : e ∈ rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D) := by
      have ht := mul_mem (inv_mem (hMC (mul_mem (mul_mem hmemb hmemc) hmemd))) hx.2
      simpa only [inv_mul_cancel_left] using ht
    have he1 : e = 1 := by
      have hr : e ∈ rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D) :=
        (rootAt_eq Q split i (Q.simple j) n hn) ▸ he
      have hz := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hr heC
      apply (MulAut.conj (n : X ⧸ Q.D)).injective
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_one] using hz
    subst e
    simpa only [one_mul, mul_one] using (mul_mem (mul_mem hmemb hmemc) hmemd)

/-- The three middle factors form a subgroup with this exact ordered product. -/
theorem middleRoots_product (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    (middleRoots Q split i j : Set (X ⧸ Q.D)) =
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxV : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) :=
      middleRoots_le_remainder Q split hm i j hij hx
    rw [radical_five_product Q split hm i j hij] at hxV
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hxV
    have hbc : b*c*d ∈ middleRoots Q split i j :=
      mul_mem (mul_mem (first_le_middle Q split i j hb) (second_le_middle Q split i j hc))
        (third_le_middle Q split i j hd)
    have haV : a ∈ simpleRemainder Q split i := by
      have ht := mul_mem (middleRoots_le_other_remainder Q split hm i j hij hx)
        (inv_mem (mul_mem (middleRoots_le_other_remainder Q split hm i j hij hbc)
          (terminal_le_other_remainder Q split hm i j hij he)))
      simpa only [mul_assoc, mul_inv_rev, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ht
    have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
    subst a
    simp only [one_mul] at hx
    have heM : e ∈ middleRoots Q split i j := by
      simpa only [inv_mul_cancel_left] using mul_mem (inv_mem hbc) hx
    have he1 : e = 1 := by
      have heC := (middleRoots_eq_intersection Q split hm i j hij
        (representative (Q.simple j)) (representative_spec _) ▸ heM).2
      have hz := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) he heC
      apply (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).injective
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_one] using hz
    subst e
    exact ⟨b*c,⟨b,hb,c,hc,rfl⟩,d,hd,by simp only [one_mul, mul_one]⟩
  · rintro x ⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,rfl⟩
    exact mul_mem (mul_mem (first_le_middle Q split i j hb) (second_le_middle Q split i j hc))
      (third_le_middle Q split i j hd)


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
