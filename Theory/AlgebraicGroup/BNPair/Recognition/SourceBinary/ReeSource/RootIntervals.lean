module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Short root intervals in the source octagon

The ordered products of two and three roots are literal intersections
of two conjugates of U. The first endpoint radical and a conjugate of the
last endpoint radical are normal in the appropriate unipotent groups.
Their commutator bounds remove the two outside factors from these unique
products. Adjacent roots therefore commute, and the commutator of roots
two positions apart lies in the intervening root.

Everything lives on the same marked quotient. The earlier (2B) panel-kernel
inclusions are explicit here and are discharged from natural markings in
the Ree MixedBounds consumer. There is no field parameter, simple-group
hypothesis, or assumed mixed relation in this geometric argument.

Source: Fong--Seitz I (1973), (3G), pp.14--16, and the bounds used in the
proof of (6H), particularly (6.2)--(6.3), printed p.52. Right conjugation
is retained for every Weyl word and normalizer representative.
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
private theorem rootAt_stabilizer_mul (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (w : Weyl Q) :
    rootAt Q split i ((longest Q*Q.simple i)*w) = rootAt Q split i w := by
  rw [← rootAt_right Q split i _ w (representative w) (representative_spec _),
    rootAt_stabilizer Q split hm i j hij]
  rfl

private theorem lengths (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
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

private theorem rootAt_right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem product_three (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    (rootIntersection split (longest Q) (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  have hh (b : Bool) := orderedRoots_product Q split b 3 (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := (hh false).symm
    change _ =
      (simpleRoot Q split 0 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rootAt Q split 0 (Q.simple 1))
        (representative (Q.simple 0) : X ⧸ Q.D) : Set (X ⧸ Q.D)) * 1)) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc, rootAt_right_rep] using ht
  · have ht := (hh true).symm
    change _ =
      (simpleRoot Q split 1 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      ((rightConjugate (rootAt Q split 1 (Q.simple 0))
        (representative (Q.simple 1) : X ⧸ Q.D) : Set (X ⧸ Q.D)) * 1)) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc, rootAt_right_rep] using ht
  · exact (hij rfl).elim

private theorem unipotent_normalizes_remainder (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i) :
    split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
  split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
    (remainder_parabolic_normalizes Q split i hK))

private theorem conjugate_disjoint (A B : Subgroup (X ⧸ Q.D))
    (h : Disjoint A B) (n : X ⧸ Q.D) :
    Disjoint (rightConjugate A n) (rightConjugate B n) := by
  apply disjoint_def.mpr
  intro x hx hy
  apply (MulAut.conj n).injective
  exact (disjoint_def.mp h hx hy).trans (map_one _).symm

/-- The three-root interval gives the (3G) mixed-root bound used in (6H).
Only the earlier panel-kernel inclusion for this root is required. -/
theorem distance_two_commutator_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
      rootAt Q split j (Q.simple i) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let g := longest Q*(Q.simple i*Q.simple j*Q.simple i)
  let n := representative g
  let V := simpleRemainder Q split i
  let R := rightConjugate V (n : X ⧸ Q.D)
  let K := rootIntersection split (longest Q) (Q.simple i*Q.simple j*Q.simple i)
  have hp : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _)*(C : Set _) :=
    product_three Q split hm i j hij
  have hA : A ≤ K := by
    intro a ha
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨a,⟨a,ha,1,one_mem _,mul_one _⟩,1,one_mem _,mul_one _⟩
  have hC : C ≤ K := by
    intro c hc
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,c,hc,one_mul _⟩
  have hl := lengths Q hm i j hij
  have hl' := lengths Q hm j i hij.symm
  have hBV : B ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i)
    · rw [sinv, hl.2.1, hl.1]
    · rw [sinv, ssq, one_mul, hl'.1, Q.tits.wordLength_one]
  have hCV : C ≤ V := by
    apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i)
    · simp only [mul_inv_rev, sinv]
      rw [hl.2.2, hl.2.1]
    · simp only [mul_inv_rev, sinv, ← mul_assoc, ssq, one_mul]
      rw [hl'.2.1, hl'.1]
  have hR : R = unipotentConjugate split g ⊓ unipotentConjugate split (Q.simple i*g) := by
    dsimp [R,V]
    rw [simpleRemainder, rightConjugate_inf,
      ← unipotentConjugate_eq split g n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _)]
  have hg : Q.simple i*g = longest Q*(Q.simple j*Q.simple i) := by
    dsimp [g]
    rw [← mul_assoc, longest_comm Q hm i j hij]
    simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul]
  have hAR : A ≤ R := by
    rw [hR]
    refine le_inf (hA.trans inf_le_right) ?_
    apply (simpleRoot_le_ascent_intersection Q split (Q.simple i*g) i ?_).trans inf_le_right
    rw [hg, mul_assoc, mul_assoc, ssq, mul_one, length_longest_mul,
      length_longest_mul, hl'.1, hl'.2.1, hm]
  have hBR : B ≤ R := by
    rw [hR]
    apply le_inf
    · apply rootAt_le_conjugate Q split j (Q.simple i) g
      simp only [sinv]
      dsimp [g]
      simp only [mul_assoc, ssq, mul_one]
      rw [length_longest_mul, length_longest_mul, hl.1, hl.2.1, hm]
    · apply rootAt_le_conjugate Q split j (Q.simple i) (Q.simple i*g)
      rw [hg, sinv]
      simp only [mul_assoc, ssq, mul_one]
      rw [length_longest_mul, wordLength_longest, hl'.1, hm]
  have hCg : rightConjugate A (n : X ⧸ Q.D) = C := by
    change rootAt Q split i g = _
    dsimp [g]
    simpa only [mul_assoc] using
      rootAt_stabilizer_mul Q split hm i j hij (Q.simple j*Q.simple i)
  have hd : Disjoint C R := by
    rw [← hCg]
    exact conjugate_disjoint Q _ _ (simpleRoot_disjoint_remainder Q split i) _
  have hN := unipotent_normalizes_remainder Q split i hK
  have hNR : unipotentConjugate split g ≤ normalizer (R : Set (X ⧸ Q.D)) := by
    change rightConjugate split.U (n : X ⧸ Q.D) ≤ _
    exact (comap_mono hN).trans (le_normalizer_comap _)
  have hcK : ⁅A,C⁆ ≤ K := (commutator_mono hA hC).trans (commutator_le_self _)
  have hcV : ⁅A,C⁆ ≤ V := (commutator_mono (simpleRoot_le Q split i) hCV).trans
    (le_normalizer_iff_commutator_le_right.mp hN)
  have hcR : ⁅A,C⁆ ≤ R := by
    rw [commutator_comm]
    exact (commutator_mono (hC.trans inf_le_right) hAR).trans
      (le_normalizer_iff_commutator_le_right.mp hNR)
  intro x hx
  have hxp : x ∈ (K : Set (X ⧸ Q.D)) := hcK hx
  rw [hp] at hxp
  obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hxp
  have haV : a ∈ V := by
    have hh := V.mul_mem (hcV hx) (V.inv_mem (V.mul_mem (hBV hb) (hCV hc)))
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh
  have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
  subst a
  simp only [one_mul] at hx
  have hcR' : c ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem (R.inv_mem (hBR hb)) (hcR hx)
  have hc1 := disjoint_def.mp hd hc hcR'
  subst c
  simpa only [one_mul, mul_one] using (show b ∈ rootAt Q split j (Q.simple i) from hb)


private theorem product_two (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    (rootIntersection split (longest Q) (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
  have hh (b : Bool) := orderedRoots_product Q split b 2 (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := (hh false).symm
    change _ =
      (simpleRoot Q split 0 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) * 1) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc] using ht
  · have ht := (hh true).symm
    change _ =
      (simpleRoot Q split 1 : Set (X ⧸ Q.D)) *
      ((rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) * 1) at ht
    simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_inv_rev, sinv, inv_one, one_mul, mul_one, mul_assoc] using ht
  · exact (hij rfl).elim

/-- Adjacent positive roots commute in the literal source octagon. -/
theorem adjacent_commutator_eq_bot (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i)⁆ = ⊥ := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let g := longest Q*(Q.simple j*Q.simple i)
  let n := representative g
  let V := simpleRemainder Q split i
  let R := rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D)
  let K := rootIntersection split (longest Q) (Q.simple j*Q.simple i)
  have hp : (K : Set (X ⧸ Q.D)) = (A : Set _)*(B : Set _) :=
    product_two Q split hm i j hij
  have hA : A ≤ K := by
    intro a ha
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨a,ha,1,one_mem _,mul_one _⟩
  have hB : B ≤ K := by
    intro b hb
    change _ ∈ (K : Set (X ⧸ Q.D))
    rw [hp]
    exact ⟨1,one_mem _,b,hb,one_mul _⟩
  have hl := lengths Q hm i j hij
  have hl' := lengths Q hm j i hij.symm
  have hBV : B ≤ V := by
    apply rootAt_le_remainder Q split j i (Q.simple i)
    · rw [sinv, hl.2.1, hl.1]
    · rw [sinv, ssq, one_mul, hl'.1, Q.tits.wordLength_one]
  have hR : R = unipotentConjugate split g ⊓ unipotentConjugate split (Q.simple j*g) := by
    dsimp [R]
    rw [simpleRemainder, rightConjugate_inf,
      ← unipotentConjugate_eq split g n (representative_spec _),
      unipotentConjugate_right split _ _ n (representative_spec _)]
  have hg : Q.simple j*g = longest Q*Q.simple i := by
    dsimp [g]
    rw [← mul_assoc, longest_comm Q hm j i hij.symm]
    simp only [mul_assoc, ← mul_assoc (Q.simple j) (Q.simple j), ssq, one_mul]
  have hAR : A ≤ R := by
    rw [hR]
    refine le_inf (hA.trans inf_le_right) ?_
    apply (simpleRoot_le_ascent_intersection Q split (Q.simple j*g) i ?_).trans inf_le_right
    rw [hg, mul_assoc, ssq, mul_one, wordLength_longest,
      wordLength_longest_mul_simple, hm]
  have hBg : rightConjugate (simpleRoot Q split j) (n : X ⧸ Q.D) = B := by
    change rootAt Q split j g = _
    dsimp [g]
    rw [← mul_assoc, rootAt_stabilizer_mul Q split hm j i hij.symm]
  have hd : Disjoint B R := by
    rw [← hBg]
    exact conjugate_disjoint Q _ _ (simpleRoot_disjoint_remainder Q split j) _
  have hNi := unipotent_normalizes_remainder Q split i hKi
  have hNj := unipotent_normalizes_remainder Q split j hKj
  have hNR : unipotentConjugate split g ≤ normalizer (R : Set (X ⧸ Q.D)) := by
    change rightConjugate split.U (n : X ⧸ Q.D) ≤ _
    exact (comap_mono hNj).trans (le_normalizer_comap _)
  have hcK : ⁅A,B⁆ ≤ K := (commutator_mono hA hB).trans (commutator_le_self _)
  have hcV : ⁅A,B⁆ ≤ V := (commutator_mono (simpleRoot_le Q split i) hBV).trans
    (le_normalizer_iff_commutator_le_right.mp hNi)
  have hcR : ⁅A,B⁆ ≤ R := by
    rw [commutator_comm]
    exact (commutator_mono (hB.trans inf_le_right) hAR).trans
      (le_normalizer_iff_commutator_le_right.mp hNR)
  apply eq_bot_iff.mpr
  intro x hx
  have hxp : x ∈ (K : Set (X ⧸ Q.D)) := hcK hx
  rw [hp] at hxp
  obtain ⟨a,ha,b,hb,rfl⟩ := hxp
  have haV : a ∈ V := by
    simpa only [mul_inv_cancel_right] using V.mul_mem (hcV hx) (V.inv_mem (hBV hb))
  have ha1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV
  subst a
  simp only [one_mul] at hx ⊢
  exact disjoint_def.mp hd hb (hcR hx)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
