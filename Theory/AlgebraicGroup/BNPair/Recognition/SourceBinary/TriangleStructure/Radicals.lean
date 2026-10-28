module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RadicalModule
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CoreCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.ElementaryAbelian.Join

/-!
# The two-root radicals of a split triangle

For rotation order three the two crossed roots coincide. Their common
subgroup is exactly the intersection of the two complementary radicals,
and each radical is the product of its two positive roots. Its derived
subgroup lies in this middle root. Normality in the full parabolic makes
the derived subgroup reflection-invariant, while the reflection sends
its middle-root support to a root disjoint from the opposite radical.
Thus both radicals are elementary when the simple roots are elementary.

The same factorization gives their square orders. The actual rank-one
reflection moves the opposite root into the middle root, proving that
the full actor acts nontrivially on the radical, including over F2.
All subgroups and conjugations belong to the same marked split quotient.

These are local structural inputs for the triangle identification in
Fong--Seitz I (3E), p.15 (which invokes Higman--McLaughlin and Abe), and
DGS (10.5), p.156. They do not assert the full projective-plane recognition.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
open RootCoordinates HexagonStructure QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simple_sq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (simple_sq Q i)
private theorem simple_cancel (i : Fin 2) (w : Weyl Q) :
    Q.simple i * (Q.simple i * w) = w := by
  rw [← mul_assoc, simple_sq, one_mul]
private theorem longest_three (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j) :
    longest Q = Q.simple i * (Q.simple j * Q.simple i) := by
  have h (b : Bool) := alternatingWord_longest Q b
  rw [hm] at h
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [alternatingWord] using (h false).symm
  · simpa [alternatingWord] using (h true).symm
  · exact (hij rfl).elim

/-- Both crossed descriptions refer to the one middle positive root. -/
theorem cross_root_intersection (hm : rotationOrder Q=3)
    (i j : Fin 2) (hij : i≠j) :
    rootAt Q split i (Q.simple j) =
      unipotentConjugate split (Q.simple j) ⊓ unipotentConjugate split (Q.simple i) := by
  have hw : (longest Q * Q.simple i) * Q.simple j = Q.simple i := by
    rw [longest_three Q hm i j hij]
    simp only [mul_assoc, simple_sq, mul_one]
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest Q * Q.simple i))
    (representative (Q.simple j) : X ⧸ Q.D) = _
  rw [rightConjugate_inf, unipotentConjugate_right split _ _ _ (representative_spec _),hw]
  rfl

theorem cross_root_eq (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j) :
    rootAt Q split i (Q.simple j) = rootAt Q split j (Q.simple i) := by
  rw [cross_root_intersection Q split hm i j hij,
    cross_root_intersection Q split hm j i hij.symm,inf_comm]

/-- The intersection is the literal middle root, inside the original U. -/
theorem radical_intersection (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j) :
    simpleRemainder Q split i ⊓ simpleRemainder Q split j =
      rootAt Q split i (Q.simple j) := by
  apply le_antisymm
  · rw [cross_root_intersection Q split hm i j hij]
    exact le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
  · have hCj := (opposite_roots_le_remainder Q split i j hij).2
    have hCi : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i := by
      rw [cross_root_eq Q split hm i j hij]
      exact (opposite_roots_le_remainder Q split j i hij.symm).2
    exact le_inf hCi hCj

private theorem remainder_product_bool (hm : rotationOrder Q=3) (b : Bool) :
    (simpleRemainder Q split (if b then 0 else 1) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) := by
  have hp := orderedRoots_product Q split b 2 (by omega)
  have hl : orderedRoots Q split b 2 =
      [simpleRoot Q split (if b then 1 else 0),
        rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0))] := by
    cases b <;> rfl
  rw [hl] at hp
  change (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) * 1) = _ at hp
  rw [mul_one] at hp
  have hw : longest Q * (alternatingWord Q b 2)⁻¹ = Q.simple (if b then 0 else 1) := by
    cases b
    · rw [longest_three Q hm 1 0 (by decide)]
      simp only [alternatingWord,Bool.not_false,Bool.false_eq_true,
        ite_false,ite_true,mul_one,mul_inv_rev,simple_inv,mul_assoc]
      simp only [simple_cancel, simple_sq, mul_one]
    · rw [longest_three Q hm 0 1 (by decide)]
      simp only [alternatingWord,Bool.not_true,Bool.false_eq_true,
        ite_false,ite_true,mul_one,mul_inv_rev,simple_inv,mul_assoc]
      simp only [simple_cancel, simple_sq, mul_one]
  rw [rootIntersection,hw] at hp
  exact hp.symm

/-- Each triangle radical is exactly a product of its two positive roots. -/
theorem remainder_product (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j) :
    (simpleRemainder Q split i : Set (X ⧸ Q.D)) =
      (simpleRoot Q split j : Set (X ⧸ Q.D)) *
        (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact remainder_product_bool Q split hm true
  · exact remainder_product_bool Q split hm false
  · exact (hij rfl).elim

theorem remainder_eq_two_roots (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j) :
    simpleRemainder Q split i = simpleRoot Q split j ⊔ rootAt Q split i (Q.simple j) := by
  rw [sup_eq_closure_mul,←remainder_product Q split hm i j hij,closure_eq]

/-- Reflection invariance of the derived radical kills its possible middle-root support. -/
theorem remainder_commutator_eq_bot (hm : rotationOrder Q=3) (i j : Fin 2) (hij : i≠j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hAj : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥) :
    ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ = ⊥ := by
  let D := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
  have hDi : D ≤ simpleRemainder Q split i :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)
  have hDj : D ≤ simpleRemainder Q split j :=
    (commutator_mono inf_le_left inf_le_left).trans
      (unipotent_commutator_le_remainder Q split j hVj hAj)
  have hDC : D ≤ rootAt Q split j (Q.simple i) := by
    rw [←cross_root_eq Q split hm i j hij,←radical_intersection Q split hm i j hij]
    exact le_inf hDi hDj
  let n := representative (Q.simple i)
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  have hconj (A B : Subgroup (X ⧸ Q.D)) :
      rightConjugate ⁅A,B⁆ (n : X ⧸ Q.D) =
        ⁅rightConjugate A (n : X ⧸ Q.D),rightConjugate B (n : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  have hfixed : rightConjugate D (n : X ⧸ Q.D) = D := by
    dsimp only [D]
    rw [hconj,rightConjugate_eq_self _ (remainder_parabolic_normalizes Q split i hVi hn)]
  have hc := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hDC
  change rightConjugate D _ ≤ rightConjugate _ _ at hc
  rw [hfixed,rootAt_right Q split j (Q.simple i) (Q.simple i) n (representative_spec _),
    simple_sq,rootAt_one] at hc
  exact bot_unique ((le_inf hc hDj).trans
    (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le)

/-- Elementary simple roots give elementary radicals in a triangle. -/
theorem remainder_elementary (hm : rotationOrder Q=3)
    (hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (hE : ∀ i, IsElementaryAbelian 2 (simpleRoot Q split i)) (i : Fin 2) :
    IsElementaryAbelian 2 (simpleRemainder Q split i) := by
  let j : Fin 2 := 1-i
  have hij : i≠j := by dsimp [j]; omega
  let := hE j
  let := rootAt_elementary Q split i (Q.simple j) (hE i)
  have hD := remainder_commutator_eq_bot Q split hm i j hij (hV i) (hV j)
    (commutator_self_eq_bot_iff.mpr inferInstance)
  have hC : ⁅rootAt Q split i (Q.simple j),simpleRoot Q split j⁆ = ⊥ := by
    apply bot_unique
    rw [←hD]
    have he := remainder_eq_two_roots Q split hm i j hij
    exact commutator_mono (he ▸ le_sup_right) (he ▸ le_sup_left)
  rw [remainder_eq_two_roots Q split hm i j hij]
  exact IsElementaryAbelian.sup_of_le_centralizer
    (commutator_eq_bot_iff_le_centralizer.mp hC)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
open Subgroup RootCoordinates HexagonStructure QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Both literal radicals have the square of the common root order. -/
theorem remainder_card (hm : rotationOrder Q = 3) (i : Fin 2) :
    Nat.card (simpleRemainder Q split i) = Nat.card (simpleRoot Q split i)^2 := by
  have hodd : Odd (rotationOrder Q) := hm ▸ (by decide : Odd 3)
  have hroot : Nat.card (simpleRoot Q split 0) = Nat.card (simpleRoot Q split i) := by
    fin_cases i
    · rfl
    · exact simpleRoot_card_eq_of_odd Q split hodd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := simpleRoot Q split i))
  rw [←unipotent_card_simple Q split i,unipotent_card_odd_pow Q split hodd,hm,hroot]
  ring

/-- The actual rank-one reflection moves the opposite root into the middle
root, so its action on the same radical is nontrivial. -/
theorem radicalAction_nontrivial (hm : rotationOrder Q = 3) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    ∃ r, radicalAction Q split i hV r ≠ 1 := by
  by_contra! hh
  let j : Fin 2 := 1-i
  have hij : i ≠ j := by dsimp [j]; omega
  let s := UnitarySource.actorReflection Q split i
  let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
  obtain ⟨a,ha,ha1⟩ := (simpleRoot Q split j).bot_or_exists_ne_one.resolve_left
    (simpleRoot_ne_bot Q split j)
  let v : simpleRemainder Q split i :=
    ⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 ha⟩
  have he := congrArg (fun f : MulAut (simpleRemainder Q split i) => (f v : X ⧸ Q.D)) (hh r⁻¹)
  rw [radicalAction_right_conjugation] at he
  change (s.val : X ⧸ Q.D)⁻¹*a*s.val = a at he
  have haC : a ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq,←he]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  have haV : a ∈ simpleRemainder Q split j := by
    rw [←cross_root_eq Q split hm i j hij] at haC
    exact (opposite_roots_le_remainder Q split i j hij).2 haC
  exact ha1 ((disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le ⟨ha,haV⟩)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure

