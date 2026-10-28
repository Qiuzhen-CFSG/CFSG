module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicRootMovement
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# The middle five-root subgroup in the degree-one octagon

The five consecutive interior roots of U_(s_i) centralize its middle odd
root. The odd-root commutators vanish by the cubic separation calculation;
the two even-root commutators are Weyl transports of adjacent commutation.
Unique ordered coordinates give the five-root subgroup order q_i³ q_j².

This subgroup is exactly V_i ∩ V_j ∩ V_j^(s_i), so it is normal in V_i.
For q_i = 2 and q_j = 4 it has order 128 and bounds the middle-root
centralizer index in V_i by sixteen. The full-radical centrality assertion
and subsequent normalizer contradiction are not assumed or proved here.

Source: Fong--Seitz I (1973), (6G), printed p.50, the first paragraph.
The original-factor and Chapter 12 applications are in
LinearPairCubicMiddleSource and LinearPairCubicMiddleChapter12.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped Pointwise MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
private theorem right_simple (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem fourth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [←right_rep]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)

/-- The two even roots adjacent to the middle odd root centralize it. -/
theorem middle_adjacent_commutators (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split j (Q.simple i*Q.simple j),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  have h := congrArg (fun A => rightConjugate A
    (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D))
    (adjacent_commutator_eq_bot Q split hm i j hij hKi hKj)
  rw [right_comm,right_simple,right_rep] at h
  simp only [right_bot,←mul_assoc] at h
  rw [fourth_root Q split hm j i hij.symm,commutator_comm] at h
  have h' := congrArg (fun A => rightConjugate A
    (representative (Q.simple i) : X ⧸ Q.D)) h
  rw [right_comm,right_rep,right_rep,fourth_root Q split hm i j hij] at h'
  simp only [mul_assoc,ssq,mul_one,right_bot] at h'
  exact ⟨h,by simpa only [mul_assoc] using h'⟩

/-- The five consecutive middle roots in the first panel radical. -/
@[expose] def middleFive (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  rootAt Q split i (Q.simple j) ⊔ rootAt Q split j (Q.simple i*Q.simple j) ⊔
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊔
    rootAt Q split i (Q.simple j*Q.simple i)

/-- The five-root subgroup centralizes the middle odd root. -/
theorem separated_middleFive_centralizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hcard : Nat.card (simpleRoot Q split i) = 2)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥) :
    middleFive Q split i j ≤
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  obtain ⟨hA,hC⟩ := separated_middle_commutators Q split hm i j hij hKi c hc
  obtain ⟨hD,hE⟩ := middle_adjacent_commutators Q split hm i j hij hKi hKj
  have hB := (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).le_normalizer.trans
    (normalizer_le_centralizer_of_card_two _ (by
      simpa only [rootAt,card_rightConjugate] using hcard))
  exact sup_le (sup_le (sup_le (sup_le
    (commutator_eq_bot_iff_le_centralizer.mp hA)
    (commutator_eq_bot_iff_le_centralizer.mp hE)) hB)
    (commutator_eq_bot_iff_le_centralizer.mp hD))
    (commutator_eq_bot_iff_le_centralizer.mp hC)


private theorem five_list (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, orderedRoots Q split b 5 =
      [simpleRoot Q split i, rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)] := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact (hij rfl).elim
  · refine ⟨false, ?_⟩
    simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, List.map_cons, List.map_nil, right_simple, right_rep,
      fourth_root Q split hm 0 1 (by decide)]
  · refine ⟨true, ?_⟩
    simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, List.map_cons, List.map_nil, right_simple, right_rep,
      fourth_root Q split hm 1 0 (by decide)]
  · exact (hij rfl).elim

private theorem five_intersection (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, middleFive Q split i j = rightConjugate
      (rootIntersection split (longest Q) (alternatingWord Q b 5)⁻¹)
      (representative (Q.simple j) : X ⧸ Q.D) ∧
      orderedRoots Q split b 5 =
      [simpleRoot Q split i, rootAt Q split j (Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)] := by
  obtain ⟨b,hb⟩ := five_list Q split hm i j hij
  have he : rootIntersection split (longest Q) (alternatingWord Q b 5)⁻¹ =
      simpleRoot Q split i ⊔ rootAt Q split j (Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p,hp⟩ := (orderedCoordinates Q split b 5 (by omega)).surjective ⟨x,hx⟩
      have hx' : rootProduct (orderedRoots Q split b 5) p = x := by
        rw [←orderedCoordinates_apply Q split b 5 (by omega)]
        exact congrArg Subtype.val hp
      rw [←hx']
      apply rootProduct_mem
      intro A hA
      rw [hb] at hA
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · have hh := orderedRoots_le Q split b 5 (by omega)
      rw [hb] at hh
      exact sup_le (sup_le (sup_le (sup_le (hh _ (by simp)) (hh _ (by simp)))
        (hh _ (by simp))) (hh _ (by simp))) (hh _ (by simp))
  refine ⟨b,?_,hb⟩
  rw [he]
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_sup]
  simp only [←comap_equiv_eq_map_symm']
  change middleFive Q split i j =
    rightConjugate (simpleRoot Q split i) (representative (Q.simple j) : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split j (Q.simple i)) (representative (Q.simple j) : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i)) (representative (Q.simple j) : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)) (representative (Q.simple j) : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) (representative (Q.simple j) : X ⧸ Q.D)
  simp only [right_simple,right_rep,mul_assoc,ssq,mul_one,middleFive]
  simp only [←mul_assoc,fourth_root Q split hm j i hij.symm]

/-- Unique root coordinates give the order of the literal middle five-root subgroup. -/
theorem middleFive_card (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (middleFive Q split i j) =
      Nat.card (simpleRoot Q split i)^3 * Nat.card (simpleRoot Q split j)^2 := by
  obtain ⟨b,he,hb⟩ := five_intersection Q split hm i j hij
  rw [he,card_rightConjugate,rootIntersection_card_ordered Q split b 5 (by omega),hb]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,rootAt,card_rightConjugate]
  ring

private theorem sinv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (ssq Q i)
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


/-- The five middle roots belong to the same literal first panel radical. -/
theorem middleFive_le_remainder (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    middleFive Q split i j ≤ simpleRemainder Q split i := by
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  apply sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  all_goals
    apply rootAt_le_remainder
    all_goals
      simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ssq,one_mul]
      simp only [←mul_assoc,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1]

/-- The degree-one centralizer already contains the paper's subgroup of order 128. -/
theorem separated_binary_middle_centralizer_card_ge (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥) :
    128 ≤ Nat.card (simpleRemainder Q split i ⊓
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) := by
  have hle := le_inf (middleFive_le_remainder Q split hm i j hij)
    (separated_middleFive_centralizes Q split hm i j hij hKi hKj hi c hc)
  have hcard : Nat.card (middleFive Q split i j) = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]
    norm_num
  rw [←hcard]
  exact Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)

private theorem middleFive_le_other_remainder (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    middleFive Q split i j ≤ simpleRemainder Q split j := by
  have hi := octagon_lengths Q i hm j hij
  have hj := octagon_lengths Q j hm i hij.symm
  apply sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  all_goals
    apply rootAt_le_remainder
    all_goals
      simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),
        ssq,one_mul]
      simp only [←mul_assoc,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
        hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2,Q.tits.wordLength_one]

private theorem right_sup (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (A ⊔ B) (representative w : X ⧸ Q.D) =
      rightConjugate A (representative w : X ⧸ Q.D) ⊔
        rightConjugate B (representative w : X ⧸ Q.D) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_sup]

/-- The simple reflection preserves the whole middle five-root subgroup. -/
theorem middleFive_reflection (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rightConjugate (middleFive Q split i j) (representative (Q.simple i) : X ⧸ Q.D) =
      middleFive Q split i j := by
  simp only [middleFive,right_sup,right_rep,mul_assoc,ssq,mul_one]
  simp only [←mul_assoc,fourth_root Q split hm i j hij]
  generalize rootAt Q split i (Q.simple j) = A
  generalize rootAt Q split i (Q.simple j*Q.simple i) = C
  generalize rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) = B
  generalize rootAt Q split j (Q.simple i*Q.simple j) = E
  generalize rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) = D
  ac_rfl

private theorem seven_list (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    ∃ b, orderedRoots Q split b 7 =
      [simpleRoot Q split j, rootAt Q split i (Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i), rootAt Q split j (Q.simple i)] ∧
      rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
        simpleRemainder Q split i := by
  have h0 := perpendicular_root_stable Q split hm i j hij
    (representative (Q.simple i)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm j i hij.symm
    (representative (Q.simple j)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) h0
  have h6 := congrArg (fun A => rightConjugate A
    (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)) h1
  simp only [right_rep, mul_assoc, ssq, mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  have hint (b : Bool) : rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
    have he : longest Q = Q.simple (if b then 0 else 1)*alternatingWord Q b 7 := by
      have hh := (alternatingWord_longest Q (!b)).symm
      rw [hm] at hh
      cases b <;> exact hh
    change split.U ⊓ unipotentConjugate split
      (longest Q*(alternatingWord Q b 7)⁻¹) = _
    rw [he,mul_inv_cancel_right]
    rfl
  have hlist (b : Bool) (hi : i = if b then 0 else 1) (hj : j = if b then 1 else 0) :
      orderedRoots Q split b 7 =
      [simpleRoot Q split j, rootAt Q split i (Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i), rootAt Q split j (Q.simple i)] := by
    cases b <;> subst i <;> subst j <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 h5 h6 <;>
      simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, List.map_cons, List.map_nil, right_simple, right_rep] <;>
      rw [h1,h5,h6] <;> simp only [mul_assoc,ssq,mul_one]
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hj : j = 1 := by omega
    subst j
    exact ⟨true,hlist true rfl rfl,hint true⟩
  · have hj : j = 0 := by omega
    subst j
    exact ⟨false,hlist false rfl rfl,hint false⟩


/-- The five-root subgroup is the intersection of three actual panel radicals. -/
theorem middleFive_eq_radical_intersection (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    middleFive Q split i j =
      (simpleRemainder Q split i ⊓ simpleRemainder Q split j) ⊓
        rightConjugate (simpleRemainder Q split j)
          (representative (Q.simple i) : X ⧸ Q.D) := by
  let R := rightConjugate (simpleRemainder Q split j)
    (representative (Q.simple i) : X ⧸ Q.D)
  have hJi := middleFive_le_remainder Q split hm i j hij
  have hJj := middleFive_le_other_remainder Q split hm i j hij
  have hJR : middleFive Q split i j ≤ R := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hJj
    change rightConjugate (middleFive Q split i j) _ ≤ R at hh
    rwa [middleFive_reflection Q split hm i j hij] at hh
  have hFj : rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split j := by
    have hi := octagon_lengths Q i hm j hij
    have hj := octagon_lengths Q j hm i hij.symm
    apply rootAt_le_remainder
    · rw [sinv,hi.2.1,hi.1]
    · rw [sinv,hj.2.2.1,hj.2.1]
  have hFR : Disjoint (rootAt Q split j (Q.simple i)) R := by
    apply disjoint_def.mpr
    intro x hx hy
    apply (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hx hy).trans (map_one _).symm
  apply le_antisymm (le_inf (le_inf hJi hJj) hJR)
  intro x hx
  obtain ⟨b,hb,hV⟩ := seven_list Q split hm i j hij
  have hp := (orderedRoots_product Q split b 7 (by omega)).symm
  rw [hV,hb] at hp
  change (simpleRemainder Q split i : Set (X ⧸ Q.D)) =
    (simpleRoot Q split j : Set (X ⧸ Q.D)) *
      ((rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) *
      ((rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
      ((rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      ((rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      ((rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) * 1)))))) at hp
  rw [mul_one] at hp
  have hxp : x ∈ (simpleRemainder Q split i : Set (X ⧸ Q.D)) := hx.1.1
  rw [hp] at hxp
  obtain ⟨u,hu,_,⟨a,ha,_,⟨e,he,_,⟨v,hv,_,⟨d,hd,_,⟨c,hc,f,hf,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hxp
  let t := a*(e*(v*(d*c)))
  have ht : t ∈ middleFive Q split i j := by
    change a*(e*(v*(d*c))) ∈
      rootAt Q split i (Q.simple j) ⊔ rootAt Q split j (Q.simple i*Q.simple j) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
        rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i)
    apply mul_mem
    · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left ha)))
    · apply mul_mem
      · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right he)))
      · apply mul_mem
        · exact mem_sup_left (mem_sup_left (mem_sup_right hv))
        · exact mul_mem (mem_sup_left (mem_sup_right hd)) (mem_sup_right hc)
  have hxj : u*(t*f) ∈ simpleRemainder Q split j := by
    have hh := hx.1.2
    change u*(a*(e*(v*(d*(c*f))))) ∈ simpleRemainder Q split j at hh
    simpa only [t,mul_assoc] using hh
  have huj : u ∈ simpleRemainder Q split j := by
    simpa only [mul_inv_cancel_right] using
      mul_mem hxj (inv_mem (mul_mem (hJj ht) (hFj hf)))
  have hu1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hu huj
  subst u
  have hxf : t*f ∈ R := by
    have hh := hx.2
    change 1*(a*(e*(v*(d*(c*f))))) ∈ R at hh
    simpa only [one_mul,t,mul_assoc] using hh
  have hfR : f ∈ R := by
    simpa only [inv_mul_cancel_left] using mul_mem (inv_mem (hJR ht)) hxf
  have hf1 := disjoint_def.mp hFR hf hfR
  subst f
  simpa only [one_mul,mul_one,t,mul_assoc] using ht

/-- The five middle roots form a normal subgroup of the full seven-root radical. -/
theorem middleFive_normalized_by_remainder (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    simpleRemainder Q split i ≤ normalizer (middleFive Q split i j : Set (X ⧸ Q.D)) := by
  have hU : split.U ≤ normalizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split j hKj))
  have hR := (comap_mono (f := (MulAut.conj
      (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hU).trans
    (le_normalizer_comap _)
  change rightConjugate split.U _ ≤ normalizer (rightConjugate (simpleRemainder Q split j) _ : Set _) at hR
  rw [middleFive_eq_radical_intersection Q split hm i j hij]
  exact (le_inf
    ((le_inf (simpleRemainder Q split i).le_normalizer (inf_le_left.trans hU)).trans
      inf_normalizer_le_normalizer_inf)
    (show simpleRemainder Q split i ≤ _ from inf_le_right.trans hR)).trans
      inf_normalizer_le_normalizer_inf

/-- In the binary branch the centralizer index in the full radical is at most sixteen. -/
theorem separated_binary_middle_centralizer_index_le (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥) :
    (simpleRemainder Q split i ⊓
      centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))).relIndex
        (simpleRemainder Q split i) ≤ 16 := by
  let C := simpleRemainder Q split i ⊓
    centralizer (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D))
  have hlo : 128 ≤ Nat.card C :=
    separated_binary_middle_centralizer_card_ge Q split hm i j hij hKi hKj hi hj c hc
  have hu := unipotent_card_even Q split 4 hm
  have he : Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1) = 8 := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · rw [hi,hj]
    · rw [hi,hj]
    · exact (hij rfl).elim
  rw [he,unipotent_card_simple Q split i,hi] at hu
  have hv : Nat.card (simpleRemainder Q split i) = 2048 := by omega
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C
    (simpleRemainder Q split i) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hv] at hh
  change C.relIndex (simpleRemainder Q split i) ≤ 16
  nlinarith
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
