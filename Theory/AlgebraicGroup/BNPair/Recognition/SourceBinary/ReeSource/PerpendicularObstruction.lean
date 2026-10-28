module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FourRootIntervals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots

/-!
# The octagon centralizer obstruction in source (6H)

The first five ordered positive roots give an injective multiplication map
on U_j^s_i, U_i^(s_j s_i), and the perpendicular root U_i^(s_j s_i s_j).
All three lie in the actual i-endpoint radical. If the two i-root
commutators vanish, this product lies in the whole radical centralizer,
whose order is consequently at least |U_j| |U_i|².

If U_i normalizes its perpendicular root, conjugation by s_j s_i s_j
exchanges the two roots. Their commutator then lies both in U_i and its
disjoint endpoint radical, so it vanishes. The natural panel markings
and (6.1) in the source consumer turn these geometric facts into the
terminal contradiction used in both parameter cases of the (6H)(b) proof.

Source: Fong--Seitz I (1973), (3G) and the proof of (6H), pp.53--54.
Right conjugation and the actual marked quotient are retained throughout.
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
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem lengths (i : Fin 2) (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j) :
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

private theorem fourth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [←right_rep]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)

private theorem five_list (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, orderedRoots Q split b 5 =
      [simpleRoot Q split i, rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)] := by
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · refine ⟨false, ?_⟩
    simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, List.map_cons, List.map_nil]
    change [simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 0) : X ⧸ Q.D),
      rightConjugate (rightConjugate (rootAt Q split 1 (Q.simple 0))
        (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D),
      rightConjugate (rightConjugate (rightConjugate (rootAt Q split 0 (Q.simple 1))
        (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D))
        (representative (Q.simple 0) : X ⧸ Q.D)] = _
    simp only [right_rep, fourth_root Q split hm 0 1 (by decide)]
  · refine ⟨true, ?_⟩
    simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, List.map_cons, List.map_nil]
    change [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D),
      rightConjugate (rightConjugate (rootAt Q split 0 (Q.simple 1))
        (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D),
      rightConjugate (rightConjugate (rightConjugate (rootAt Q split 1 (Q.simple 0))
        (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D))
        (representative (Q.simple 1) : X ⧸ Q.D)] = _
    simp only [right_rep, fourth_root Q split hm 1 0 (by decide)]
  · exact (hij rfl).elim

theorem octagon_three_roots_le_remainder (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split i ∧
    rootAt Q split i (Q.simple j*Q.simple i) ≤ simpleRemainder Q split i ∧
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ simpleRemainder Q split i := by
  have hi := lengths Q i hm j hij
  have hj := lengths Q j hm i hij.symm
  refine ⟨?_,?_,?_⟩
  · apply rootAt_le_remainder Q split j i (Q.simple i)
    · rw [sinv, hi.2.1, hi.1]
    · rw [sinv, ssq, one_mul, hj.1, Q.tits.wordLength_one]
  · apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i)
    · simp only [mul_inv_rev, sinv]
      rw [hi.2.2.1, hi.2.1]
    · simp only [mul_inv_rev, sinv, ←mul_assoc, ssq, one_mul]
      rw [hj.2.1, hj.1]
  · apply rootAt_le_remainder Q split i i (Q.simple j*Q.simple i*Q.simple j)
    · simp only [mul_inv_rev, sinv, ←mul_assoc]
      rw [hj.2.2.2.1, hj.2.2.1]
    · simp only [mul_inv_rev, sinv, ←mul_assoc]
      rw [hi.2.2.2.2, hi.2.2.2.1]

/-- Unique ordered multiplication for the three roots used in the p.53 centralizer contradiction. -/
theorem octagon_three_root_product_injective (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Function.Injective (fun p : rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) =>
      (p.1 : X ⧸ Q.D)*(p.2.1 : X ⧸ Q.D)*(p.2.2 : X ⧸ Q.D)) := by
  obtain ⟨b,hb⟩ := five_list Q split hm i j hij
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b 5)) := by
    intro p q he
    apply (orderedCoordinates Q split b 5 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [hb] at hinj
  intro p q he
  have hh := hinj (a₁ := (1,p.1,p.2.1,1,p.2.2,PUnit.unit))
    (a₂ := (1,q.1,q.2.1,1,q.2.2,PUnit.unit)) (by
      simpa only [rootProduct, OneMemClass.coe_one, one_mul, mul_one, mul_assoc] using he)
  exact Prod.ext (congrArg (fun z => z.2.1) hh)
    (Prod.ext (congrArg (fun z => z.2.2.1) hh) (congrArg (fun z => z.2.2.2.2.1) hh))

/-- Normalizing the perpendicular root forces commutation, by reflection and disjoint radicals. -/
theorem perpendicular_commutator_eq_bot_of_normalizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (hn : simpleRoot Q split i ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  let A := simpleRoot Q split i
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let V := simpleRemainder Q split i
  let w := Q.simple j*Q.simple i*Q.simple j
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he (K : Subgroup (X ⧸ Q.D)) : K.map e.toMonoidHom =
      rightConjugate K (representative w : X ⧸ Q.D) := by
    simp only [rightConjugate, comap_equiv_eq_map_symm']; rfl
  have hEA : E.map e.toMonoidHom = A := by
    rw [he]
    change rightConjugate (rootAt Q split i w) (representative w : X ⧸ Q.D) = A
    rw [right_rep]
    dsimp only [w,A]
    simp only [mul_assoc, ←mul_assoc (Q.simple j) (Q.simple j),
      ←mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul, rootAt_one]
  have hAE : A.map e.toMonoidHom = E := by rw [he]; rfl
  have hN := split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
    (remainder_parabolic_normalizes Q split i hK))
  have hV : ⁅A,E⁆ ≤ V :=
    (commutator_mono (simpleRoot_le Q split i)
      (octagon_three_roots_le_remainder Q split hm i j hij).2.2).trans
        (le_normalizer_iff_commutator_le_right.mp hN)
  have hE : ⁅A,E⁆ ≤ E := le_normalizer_iff_commutator_le_right.mp hn
  have hA : ⁅A,E⁆ ≤ A := by
    have hh := map_mono (f := e.toMonoidHom) hE
    rw [map_commutator,hAE,hEA,commutator_comm] at hh
    exact hh
  exact eq_bot_iff.mpr (le_inf hA hV |>.trans (simpleRoot_disjoint_remainder Q split i).le_bot)

/-- The three independent root factors give a lower bound on the whole radical centralizer. -/
theorem octagon_centralizer_card_ge_of_two_commutators
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hperp : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    Nat.card (simpleRoot Q split j)*Nat.card (simpleRoot Q split i)^2 ≤
      Nat.card (simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let D := simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))
  have hV := octagon_three_roots_le_remainder Q split hm i j hij
  have hB : B ≤ D := le_inf hV.1 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (adjacent_commutator_eq_bot Q split hm i j hij hKi hKj)))
  have hC : C ≤ D := le_inf hV.2.1 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans hnear))
  have hE : E ≤ D := le_inf hV.2.2 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans hperp))
  let f : B × C × E → D := fun p =>
    ⟨(p.1 : X ⧸ Q.D)*(p.2.1 : X ⧸ Q.D)*(p.2.2 : X ⧸ Q.D),
      D.mul_mem (D.mul_mem (hB p.1.property) (hC p.2.1.property)) (hE p.2.2.property)⟩
  have hf : Function.Injective f := by
    intro p q he
    exact octagon_three_root_product_injective Q split hm i j hij (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_injective f hf
  have hc (k : Fin 2) (w : Weyl Q) : Nat.card (rootAt Q split k w) = Nat.card (simpleRoot Q split k) :=
    Nat.card_congr (rightConjugateEquiv (simpleRoot Q split k) (representative w)).symm
  simp only [Nat.card_prod] at hh
  dsimp only [B,C,E] at hh
  rw [hc,hc,hc] at hh
  simpa only [pow_two] using hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
