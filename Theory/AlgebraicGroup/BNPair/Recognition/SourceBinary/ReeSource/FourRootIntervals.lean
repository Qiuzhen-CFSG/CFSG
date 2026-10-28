module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RootIntervals

/-!
# Four-root intervals and their reflected derived placement

The ordered product of four consecutive roots is an intersection of two
unipotent groups. Normality of the two endpoint radicals removes the outside
factors from their commutator, leaving the actual product of the two middle
roots. Reflection by s_j s_i s_j fixes the middle i-root, exchanges the two
j-roots, and places both commutator arguments in the i-endpoint radical.
Thus the reflected commutator lies in its derived subgroup.

Source: Fong--Seitz I (1973), (3G), and the geometric placements preceding
(6.4), printed p.52. All subgroups and conjugations are on the same marked
quotient. The panel-kernel inputs are discharged by natural markings in
ReeSource.SixFourSupport; no mixed relation or common field is assumed here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem sinv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (ssq Q i)
private theorem longest_eight (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
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
private theorem longest_comm (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.simple i * longest Q = longest Q * Q.simple i := by
  conv_lhs => rw [longest_eight Q hm i j hij]
  conv_rhs => rw [longest_eight Q hm j i hij.symm]
  simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i), ssq,
    one_mul, mul_one]
private theorem rootAt_stabilizer (hm : rotationOrder Q = 8)
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
theorem rootAt_longest_simple_mul (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (w : Weyl Q) :
    rootAt Q split i ((longest Q*Q.simple i)*w) = rootAt Q split i w := by
  rw [← rootAt_right Q split i _ w (representative w) (representative_spec _),
    rootAt_stabilizer Q split hm i j hij]
  rfl

private theorem octagon_lengths (i : Fin 2) (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 4 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 5 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

private theorem rootAt_right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem product_four (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    (rootIntersection split (longest Q) (Q.simple j*Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  have hh (b : Bool) := orderedRoots_product Q split b 4 (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := (hh false).symm
    change _ = (simpleRoot Q split 0 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rootAt Q split 0 (Q.simple 1))
        (representative (Q.simple 0) : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rightConjugate (rootAt Q split 1 (Q.simple 0))
        (representative (Q.simple 1) : X ⧸ Q.D))
        (representative (Q.simple 0) : X ⧸ Q.D) : Set (X ⧸ Q.D)) * 1))) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc, rootAt_right_rep] using ht
  · have ht := (hh true).symm
    change _ = (simpleRoot Q split 1 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rootAt Q split 1 (Q.simple 0))
        (representative (Q.simple 1) : X ⧸ Q.D) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rightConjugate (rootAt Q split 0 (Q.simple 1))
        (representative (Q.simple 0) : X ⧸ Q.D))
        (representative (Q.simple 1) : X ⧸ Q.D) : Set (X ⧸ Q.D)) * 1))) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc, rootAt_right_rep] using ht
  · exact (hij rfl).elim

/-- The endpoints of a four-root interval have commutators in its two middle roots. -/
theorem distance_three_commutator_support (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆) :
    x ∈ (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let g := longest Q*(Q.simple j*Q.simple i*Q.simple j*Q.simple i)
  let n := representative g
  let V := simpleRemainder Q split i
  let R := rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D)
  let K := rootIntersection split (longest Q) (Q.simple j*Q.simple i*Q.simple j*Q.simple i)
  have hp : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _)*(C : Set _)*(D : Set _) :=
    product_four Q split hm i j hij
  have hA : A ≤ K := by
    intro a ha
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨a,⟨a,⟨a,ha,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hD : D ≤ K := by
    intro d hd
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,d,hd,one_mul _⟩
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  have hBV : B ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i)
    · rw [sinv,hi.2.1,hi.1]
    · rw [sinv,ssq,one_mul,hj.1,Q.tits.wordLength_one]
  have hCV : C ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i)
    · simp only [mul_inv_rev,sinv]; rw [hi.2.2.1,hi.2.1]
    · simp only [mul_inv_rev,sinv,←mul_assoc,ssq,one_mul]; rw [hj.2.1,hj.1]
  have hDV : D ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i*Q.simple j*Q.simple i)
    · simp only [mul_inv_rev,sinv,←mul_assoc]; rw [hi.2.2.2.1,hi.2.2.1]
    · simp only [mul_inv_rev,sinv,←mul_assoc,ssq,one_mul]; rw [hj.2.2.1,hj.2.1]
  have hR : R = unipotentConjugate split g ⊓ unipotentConjugate split (Q.simple j*g) := by
    dsimp [R]
    rw [simpleRemainder,rightConjugate_inf,
      ←unipotentConjugate_eq split g n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _)]
  have hg : Q.simple j*g = longest Q*(Q.simple i*Q.simple j*Q.simple i) := by
    dsimp [g]
    rw [←mul_assoc,longest_comm Q hm j i hij.symm]
    simp only [mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul]
  have hAR : A ≤ R := by
    rw [hR]
    refine le_inf (hA.trans inf_le_right) ?_
    apply (simpleRoot_le_ascent_intersection Q split (Q.simple j*g) i ?_).trans inf_le_right
    rw [hg,mul_assoc,mul_assoc,ssq,mul_one,length_longest_mul,length_longest_mul,
      hi.2.1,hi.2.2.1,hm]
  have hBR : B ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i) g
      simp only [sinv]; dsimp [g]
      simp only [mul_assoc,ssq,mul_one]
      rw [length_longest_mul,length_longest_mul]
      simp only [←mul_assoc,hj.2.1,hj.2.2.1,hm]
    · apply rootAt_le_conjugate Q split j (Q.simple i) (Q.simple j*g)
      rw [hg,sinv]
      simp only [mul_assoc,ssq,mul_one]
      rw [length_longest_mul,length_longest_mul,hi.1,hi.2.1,hm]
  have hCR : C ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) g
      simp only [mul_inv_rev,sinv]; dsimp [g]
      simp only [mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,mul_one]
      rw [length_longest_mul,length_longest_mul,hj.1,hj.2.1,hm]
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) (Q.simple j*g)
      rw [hg]
      simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,mul_one]
      rw [wordLength_longest,length_longest_mul,hi.1,hm]
  have hDg : rightConjugate (simpleRoot Q split j) (n : X ⧸ Q.D) = D := by
    change rootAt Q split j g = _
    dsimp [g,D]
    simpa only [mul_assoc] using
      rootAt_longest_simple_mul Q split hm j i hij.symm (Q.simple i*Q.simple j*Q.simple i)
  have hd : Disjoint D R := by
    rw [←hDg]
    apply disjoint_def.mpr
    intro x hx hy
    apply (MulAut.conj (n : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hx hy).trans (map_one _).symm
  have hN (k : Fin 2) (hK : simpleRemainder Q split k ≤ localKernel Q k) :
      split.U ≤ normalizer (simpleRemainder Q split k : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split k hK))
  have hNR : unipotentConjugate split g ≤ normalizer (R : Set (X ⧸ Q.D)) := by
    change rightConjugate split.U (n : X ⧸ Q.D) ≤ _
    exact (comap_mono (hN j hKj)).trans (le_normalizer_comap _)
  have hcK : ⁅A,D⁆ ≤ K := (commutator_mono hA hD).trans (commutator_le_self _)
  have hcV : ⁅A,D⁆ ≤ V := (commutator_mono (simpleRoot_le Q split i) hDV).trans
    (le_normalizer_iff_commutator_le_right.mp (hN i hKi))
  have hcR : ⁅A,D⁆ ≤ R := by
    rw [commutator_comm]
    exact (commutator_mono (hD.trans inf_le_right) hAR).trans
      (le_normalizer_iff_commutator_le_right.mp hNR)
  have hxp : x ∈ (K : Set (X ⧸ Q.D)) := hcK hx
  rw [hp] at hxp
  obtain ⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd',rfl⟩ := hxp
  have haV : a ∈ V := by
    have hh := V.mul_mem (hcV hx) (V.inv_mem (V.mul_mem (V.mul_mem (hBV hb) (hCV hc)) (hDV hd')))
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
  subst a
  simp only [one_mul] at hx ⊢
  have hdR : d ∈ R := by
    simpa only [inv_mul_cancel_left] using
      R.mul_mem (R.inv_mem (R.mul_mem (hBR hb) (hCR hc))) (hcR hx)
  have hd1 := disjoint_def.mp hd hd' hdR
  subst d
  simpa only [mul_one] using (show b*c ∈ (B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D)) from ⟨b,hb,c,hc,rfl⟩)


/-- The three Weyl identities for the conjugation used before source (6.4). -/
theorem four_interval_reflection (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i*Q.simple j) :
    rightConjugate (rootAt Q split j (Q.simple i)) (n : X ⧸ Q.D) =
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ∧
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i)) (n : X ⧸ Q.D) =
        rootAt Q split i (Q.simple j*Q.simple i) ∧
    rightConjugate (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)) (n : X ⧸ Q.D) =
        rootAt Q split j (Q.simple i) := by
  simp only [rootAt_right Q split _ _ _ n hn]
  have hi := longest_eight Q hm i j hij
  have hj := longest_eight Q hm j i hij.symm
  refine ⟨?_,?_,?_⟩
  · have he : Q.simple i*(Q.simple j*Q.simple i*Q.simple j) =
        (longest Q*Q.simple j)*(Q.simple i*Q.simple j*Q.simple i) := by
      rw [hi]
      simp only [mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
    rw [he,rootAt_longest_simple_mul Q split hm j i hij.symm]
  · have he : (Q.simple j*Q.simple i)*(Q.simple j*Q.simple i*Q.simple j) =
        (longest Q*Q.simple i)*(Q.simple j*Q.simple i) := by
      rw [hj]
      simp only [mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
    rw [he,rootAt_longest_simple_mul Q split hm i j hij]
  · have he : (Q.simple i*Q.simple j*Q.simple i)*(Q.simple j*Q.simple i*Q.simple j) =
        (longest Q*Q.simple j)*Q.simple i := by
      rw [hi]
      simp only [mul_assoc,ssq,mul_one]
    rw [he,rootAt_longest_simple_mul Q split hm j i hij.symm]

/-- The reflected mixed commutator lies in the actual derived radical. -/
theorem four_interval_reflected_derived (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i*Q.simple j) :
    rightConjugate ⁅simpleRoot Q split i,
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ (n : X ⧸ Q.D) ≤
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
  have hconj (A B : Subgroup (X ⧸ Q.D)) :
      rightConjugate ⁅A,B⁆ (n : X ⧸ Q.D) =
        ⁅rightConjugate A (n : X ⧸ Q.D),rightConjugate B (n : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  rw [hconj,(four_interval_reflection Q split hm i j hij n hn).2.2]
  have hA : rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
    rw [←rootAt_one Q split i,rootAt_right Q split i 1 _ n hn,one_mul]
  rw [hA]
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  apply commutator_mono
  · apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i*Q.simple j)
    · simp only [mul_inv_rev,sinv,←mul_assoc]; rw [hj.2.2.2.1,hj.2.2.1]
    · simp only [mul_inv_rev,sinv,←mul_assoc]; rw [hi.2.2.2.2,hi.2.2.2.1]
  · apply rootAt_le_remainder Q split j i (Q.simple i)
    · rw [sinv,hi.2.1,hi.1]
    · rw [sinv,ssq,one_mul,hj.1,Q.tits.wordLength_one]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
