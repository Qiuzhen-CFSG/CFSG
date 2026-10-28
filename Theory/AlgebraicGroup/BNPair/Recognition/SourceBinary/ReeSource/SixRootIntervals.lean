module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PerpendicularObstruction

/-!
# Six-root support in the source octagon

The six consecutive roots form a literal intersection of two unipotent
subgroups. The two endpoint radicals are normal in the respective
unipotent groups. Their commutator bounds and the unique ordered product
remove both outside factors, leaving the four interior roots.

This is the six-root instance of Fong--Seitz I (1973), (3G), pp.14--16,
used in the three-subgroup argument on p.53. BinaryTerminal applies the
bound to the actual source roots. No mixed relation or field identification
is assumed here; the preceding panel-kernel containments remain explicit.
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
    Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 7 := by
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 5) (by omega))
    (And.intro (wordLength_alternatingWord Q b (n := 6) (by omega))
      (wordLength_alternatingWord Q b (n := 7) (by omega)))))))
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

private theorem fifth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split j (Q.simple i*Q.simple j) := by
  have he : Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i =
      (longest Q*Q.simple j)*(Q.simple i*Q.simple j) := by
    rw [longest_eight Q hm i j hij]
    simp only [mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul, mul_one]
  rw [he, rootAt_longest_simple_mul Q split hm j i hij.symm]

private theorem simple_rep (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl

private theorem product_six (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ((split.U ⊓ unipotentConjugate split (Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) * (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  have hg : longest Q*(Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      Q.simple i*Q.simple j := by
    rw [longest_eight Q hm i j hij]
    simp only [mul_assoc, ←mul_assoc (Q.simple j) (Q.simple j),
      ←mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul, mul_one]
  have hh (b : Bool) := (orderedRoots_product Q split b 6 (by omega)).symm
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := hh false
    change _ = (simpleRoot Q split 0 : Set (X ⧸ Q.D)) * (((rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * 1))))) at ht
    simp only [simple_rep, right_rep, fourth_root Q split hm 0 1 (by decide),
      fifth_root Q split hm 0 1 (by decide), alternatingWord, Bool.false_eq_true,
      ↓reduceIte, Bool.not_false, Bool.not_true, mul_inv_rev, sinv, mul_one, rootIntersection] at ht
    rw [hg] at ht
    simpa only [mul_assoc] using ht
  · have ht := hh true
    change _ = (simpleRoot Q split 1 : Set (X ⧸ Q.D)) * (((rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 1) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * (((rightConjugate (rightConjugate (rightConjugate (rightConjugate (rightConjugate (simpleRoot Q split 0) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D)) : Set (X ⧸ Q.D)) * 1))))) at ht
    simp only [simple_rep, right_rep, fourth_root Q split hm 1 0 (by decide),
      fifth_root Q split hm 1 0 (by decide), alternatingWord, Bool.false_eq_true,
      ↓reduceIte, Bool.not_false, Bool.not_true, mul_inv_rev, sinv, mul_one, rootIntersection] at ht
    rw [hg] at ht
    simpa only [mul_assoc] using ht
  · exact (hij rfl).elim

set_option linter.unusedSimpArgs false in
/-- The six-root interval bounds its endpoint commutator by the four interior roots. -/
theorem distance_five_commutator_support (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (x : X ⧸ Q.D)
    (hx : x ∈ ⁅simpleRoot Q split i, rootAt Q split j (Q.simple i*Q.simple j)⁆) :
    x ∈ (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let F := rootAt Q split j (Q.simple i*Q.simple j)
  let g := Q.simple i*Q.simple j
  let n := representative g
  let V := simpleRemainder Q split i
  let R := rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D)
  let K := split.U ⊓ unipotentConjugate split g
  have hp : (K : Set (X ⧸ Q.D)) =
      (A : Set (X ⧸ Q.D))*(B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D))*(D : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D))*(F : Set (X ⧸ Q.D)) :=
    product_six Q split hm i j hij
  have hA : A ≤ K := by
    intro a ha
    change a ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨a,⟨a,⟨a,⟨a,⟨a,ha,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,
      1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hF : F ≤ K := by
    intro f hf
    change f ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,⟨1,⟨1,⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,
      1,one_mem _,one_mul _⟩,1,one_mem _,one_mul _⟩,f,hf,one_mul _⟩
  have hi := lengths Q hm i j hij
  have hj := lengths Q hm j i hij.symm
  have hBV : B ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i) <;>
    simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one] <;>
    simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hCV : C ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i) <;>
    simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one] <;>
    simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hDV : D ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i*Q.simple j*Q.simple i) <;>
    simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one] <;>
    simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hEV : E ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i*Q.simple j) <;>
    simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one] <;>
    simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hFV : F ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i*Q.simple j) <;>
    simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one] <;>
    simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hR : R = unipotentConjugate split g ⊓ unipotentConjugate split (Q.simple j*g) := by
    dsimp only [R]
    rw [simpleRemainder, rightConjugate_inf,
      ←unipotentConjugate_eq split g n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _)]
  have hAR : A ≤ R := by
    rw [hR]
    dsimp only [A]
    rw [←rootAt_one Q split i]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (1) g
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split i (1) (Q.simple j*g)
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hBR : B ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i) g
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split j (Q.simple i) (Q.simple j*g)
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hCR : C ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) g
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i) (Q.simple j*g)
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hDR : D ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i*Q.simple j*Q.simple i) g
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split j (Q.simple i*Q.simple j*Q.simple i) (Q.simple j*g)
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hER : E ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i*Q.simple j) g
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
    · apply rootAt_le_conjugate Q split i (Q.simple j*Q.simple i*Q.simple j) (Q.simple j*g)
      dsimp only [g]
      simp only [inv_one, mul_inv_rev, sinv, mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul, mul_one]
      simp only [←mul_assoc, Q.tits.wordLength_one, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]
  have hd : Disjoint F R := by
    change Disjoint (rightConjugate (simpleRoot Q split j) (n : X ⧸ Q.D)) R
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
  have hcK : ⁅A,F⁆ ≤ K := (commutator_mono hA hF).trans (commutator_le_self _)
  have hcV : ⁅A,F⁆ ≤ V := (commutator_mono (simpleRoot_le Q split i) hFV).trans
    (le_normalizer_iff_commutator_le_right.mp (hN i hKi))
  have hcR : ⁅A,F⁆ ≤ R := by
    rw [commutator_comm]
    exact (commutator_mono (hF.trans inf_le_right) hAR).trans
      (le_normalizer_iff_commutator_le_right.mp hNR)
  have hxp : x ∈ (K : Set (X ⧸ Q.D)) := hcK hx
  rw [hp] at hxp
  obtain ⟨abcde,⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd',rfl⟩,e,he,rfl⟩,f,hf,rfl⟩ := hxp
  have haV : a ∈ V := by
    have hh := V.mul_mem (hcV hx) (V.inv_mem (V.mul_mem
      (V.mul_mem (V.mul_mem (V.mul_mem (hBV hb) (hCV hc)) (hDV hd')) (hEV he)) (hFV hf)))
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
  subst a
  simp only [one_mul] at hx ⊢
  have hfR : f ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem
      (R.inv_mem (R.mul_mem (R.mul_mem (R.mul_mem (hBR hb) (hCR hc)) (hDR hd')) (hER he))) (hcR hx)
  have hf1 := disjoint_def.mp hd hf hfR
  subst f
  simpa only [mul_one] using
    (show b*c*d*e ∈ (B : Set (X ⧸ Q.D))*(C : Set (X ⧸ Q.D))*(D : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D)) from
      ⟨b*c*d,⟨b*c,⟨b,hb,c,hc,rfl⟩,d,hd',rfl⟩,e,he,rfl⟩)

private theorem eight_list (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, orderedRoots Q split b 8 =
      [simpleRoot Q split i, rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j),
       rootAt Q split i (Q.simple j), simpleRoot Q split j] := by
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · refine ⟨false,?_⟩
    simp only [orderedRoots, List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, simple_rep, right_rep,
      fourth_root Q split hm 0 1 (by decide), fifth_root Q split hm 0 1 (by decide)]
    simp only [mul_assoc, ssq, mul_one, rootAt_one]
  · refine ⟨true,?_⟩
    simp only [orderedRoots, List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, simple_rep, right_rep,
      fourth_root Q split hm 1 0 (by decide), fifth_root Q split hm 1 0 (by decide)]
    simp only [mul_assoc, ssq, mul_one, rootAt_one]
  · exact (hij rfl).elim

/-- The six roots on either side of the perpendicular root retain unique ordered multiplication. -/
theorem octagon_six_root_product_injective (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Function.Injective (fun p : rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j) ×
      rootAt Q split i (Q.simple j) × simpleRoot Q split j =>
      (p.1 : X ⧸ Q.D)*(p.2.1 : X ⧸ Q.D)*(p.2.2.1 : X ⧸ Q.D)*
        (p.2.2.2.1 : X ⧸ Q.D)*(p.2.2.2.2.1 : X ⧸ Q.D)*(p.2.2.2.2.2 : X ⧸ Q.D)) := by
  obtain ⟨b,hb⟩ := eight_list Q split hm i j hij
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b 8)) := by
    intro p q he
    apply (orderedCoordinates Q split b 8 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [hb] at hinj
  intro p q he
  have hh := hinj (a₁ := (1,p.1,p.2.1,p.2.2.1,1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2,PUnit.unit))
    (a₂ := (1,q.1,q.2.1,q.2.2.1,1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2,PUnit.unit)) (by
      simpa only [rootProduct, OneMemClass.coe_one, one_mul, mul_one, mul_assoc] using he)
  exact Prod.ext (congrArg (fun z => z.2.1) hh)
    (Prod.ext (congrArg (fun z => z.2.2.1) hh)
      (Prod.ext (congrArg (fun z => z.2.2.2.1) hh)
        (Prod.ext (congrArg (fun z => z.2.2.2.2.2.1) hh)
          (Prod.ext (congrArg (fun z => z.2.2.2.2.2.2.1) hh)
            (congrArg (fun z => z.2.2.2.2.2.2.2.1) hh)))))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
