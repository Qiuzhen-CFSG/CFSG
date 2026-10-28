module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PerpendicularObstruction

/-!
# Perpendicular commutator support in the source octagon

The five consecutive roots form a literal intersection of two unipotent
subgroups. Normality of the first endpoint radical and its conjugate at
the last endpoint removes both outside coordinates from the commutator.
Thus the perpendicular-root commutator lies in the three interior roots.

Source: Fong--Seitz I (1973), (3G), pp.14--16, used in (6H)(b), p.53.
The positive near-equality consumer uses this support in the simultaneous
zero branch. Only the actual panel-kernel containment is required.
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
private theorem lengths (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple i) = 1 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j) = 2 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i) = 3 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 4 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 5 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 6 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 7 ∧
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 8 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 5) (by omega))
    (And.intro (wordLength_alternatingWord Q b (n := 6) (by omega))
      (And.intro (wordLength_alternatingWord Q b (n := 7) (by omega))
      (wordLength_alternatingWord Q b (n := 8) (by omega))))))))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh false
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using hh true
  · exact (hij rfl).elim

private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem fourth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [←right_rep]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)

private theorem simple_rep (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) = rootAt Q split i w := rfl

private theorem product_five (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ((split.U ⊓ unipotentConjugate split (Q.simple j*Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) * (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  have hg : longest Q*(Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      Q.simple j*Q.simple i*Q.simple j := by
    rw [longest_eight Q hm j i hij.symm]
    simp only [mul_assoc, ←mul_assoc (Q.simple j) (Q.simple j),
      ←mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul, mul_one]
  have hh (b : Bool) := (orderedRoots_product Q split b 5 (by omega)).symm
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := hh false
    change _ = ((simpleRoot Q split 0) : Set (X ⧸ Q.D)) * (((rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (1))))) at ht
    simp only [simple_rep,right_rep,fourth_root Q split hm 0 1 (by decide),
      alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
      mul_inv_rev,sinv,mul_one,rootIntersection] at ht
    rw [hg] at ht
    simpa only [mul_assoc] using ht
  · have ht := hh true
    change _ = ((simpleRoot Q split 1) : Set (X ⧸ Q.D)) * (((rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (1))))) at ht
    simp only [simple_rep,right_rep,fourth_root Q split hm 1 0 (by decide),
      alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
      mul_inv_rev,sinv,mul_one,rootIntersection] at ht
    rw [hg] at ht
    simpa only [mul_assoc] using ht
  · exact (hij rfl).elim

set_option linter.unusedSimpArgs false in
/-- The perpendicular endpoint commutator lies in the three interior roots. -/
theorem distance_four_commutator_support (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆) :
    x ∈ (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let g := Q.simple j*Q.simple i*Q.simple j
  let n := representative g
  let V := simpleRemainder Q split i
  let R := rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D)
  let K := split.U ⊓ unipotentConjugate split g
  have hp : (K : Set (X ⧸ Q.D)) =
      (A : Set (X ⧸ Q.D))*(B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D))*(D : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D)) :=
    product_five Q split hm i j hij
  have hA : A ≤ K := by
    intro a ha
    change a ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨a,⟨a,⟨a,⟨a,ha,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,
      1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hE : E ≤ K := by
    intro e he
    change e ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,⟨1,⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,
      1,one_mem _,one_mul _⟩,e,he,one_mul _⟩
  have hi := lengths Q hm i j hij
  have hj := lengths Q hm j i hij.symm
  have hBV : B ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i) <;>
    simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one] <;>
    simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
      hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
      hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hCV : C ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i) <;>
    simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one] <;>
    simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
      hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
      hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hDV : D ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i*Q.simple j*Q.simple i) <;>
    simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one] <;>
    simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
      hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
      hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hEV : E ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i*Q.simple j) <;>
    simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one] <;>
    simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
      hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
      hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hR : R = unipotentConjugate split g ⊓ unipotentConjugate split (Q.simple i*g) := by
    dsimp only [R]
    rw [simpleRemainder,rightConjugate_inf,←unipotentConjugate_eq split g n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _)]
  have hAR : A ≤ R := by
    rw [hR]
    dsimp only [A]
    rw [←rootAt_one Q split i]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (1) g
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split i (1) (Q.simple i*g)
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hBR : B ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i) g
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split j (Q.simple i) (Q.simple i*g)
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hCR : C ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) g
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) (Q.simple i*g)
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hDR : D ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i*Q.simple j*Q.simple i) g
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split j (Q.simple i*Q.simple j*Q.simple i) (Q.simple i*g)
      dsimp only [g]
      simp only [inv_one,mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul,mul_one]
      simp only [←mul_assoc,Q.tits.wordLength_one,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2.1,hi.2.2.2.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,
        hj.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2]
  have hd : Disjoint E R := by
    change Disjoint (rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) R
    apply disjoint_def.mpr
    intro x hx hy
    apply (MulAut.conj (n : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hx hy).trans (map_one _).symm
  have hN : split.U ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hKi))
  have hNR : unipotentConjugate split g ≤ normalizer (R : Set (X ⧸ Q.D)) := by
    change rightConjugate split.U (n : X ⧸ Q.D) ≤ _
    exact (comap_mono hN).trans (le_normalizer_comap _)
  have hcK : ⁅A,E⁆ ≤ K := (commutator_mono hA hE).trans (commutator_le_self _)
  have hcV : ⁅A,E⁆ ≤ V := (commutator_mono (simpleRoot_le Q split i) hEV).trans
    (le_normalizer_iff_commutator_le_right.mp hN)
  have hcR : ⁅A,E⁆ ≤ R := by
    rw [commutator_comm]
    exact (commutator_mono (hE.trans inf_le_right) hAR).trans
      (le_normalizer_iff_commutator_le_right.mp hNR)
  have hxp : x ∈ (K : Set (X ⧸ Q.D)) := hcK hx
  rw [hp] at hxp
  obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd',rfl⟩,e,he,rfl⟩ := hxp
  have haV : a ∈ V := by
    have hh := V.mul_mem (hcV hx) (V.inv_mem (V.mul_mem
      (V.mul_mem (V.mul_mem (hBV hb) (hCV hc)) (hDV hd')) (hEV he)))
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
  subst a
  simp only [one_mul] at hx ⊢
  have heR : e ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem
      (R.inv_mem (R.mul_mem (R.mul_mem (hBR hb) (hCR hc)) (hDR hd'))) (hcR hx)
  have he1 := disjoint_def.mp hd he heR
  subst e
  simpa only [mul_one] using
    (show b*c*d ∈ (B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D))*(D : Set (X ⧸ Q.D)) from
      ⟨b*c,⟨b,hb,c,hc,rfl⟩,d,hd',rfl⟩)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
