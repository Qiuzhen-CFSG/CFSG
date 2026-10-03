module

public import Theory.GroupTheory.FinitePredicateSeparation
public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Lower small even node witnesses, batch F

For each listed node, products of squares certify the generator displacements.
A Boolean mask on the first few root coordinates contains the identity, is
preserved by right multiplication by every generator, and excludes the witness.
The finite predicate separation lemma proves nonmembership; the square-word
criterion then gives normalization and trivial Frattini action.

The complement-action tables reduce transition checks to the triangular core
multiplication formulas. The tables, transitions, separating values, and square
identities are all checked by kernel reduction. The original node definitions
and their generator order are retained.

Source: Shinoda (1975), (2.3), pp. 81–82, via the verified Ree two coordinates.
Exploratory square words and masks only guide these independently checked proofs.
-/

namespace ReeTwo.SylowModel.SmallEvenLower
set_option maxRecDepth 10000

namespace Node248
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 248 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[1]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (107839786693710966126060789954106421527956964701823053292292930535425 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 248 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 248).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node248

namespace Node249
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 249 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0, 1]], [[1, 3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 249 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 249).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node249

namespace Node250
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 250 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [], [[1, 3], [1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (12486994201990807650498917121802605602414726854123866783199000155091142251864643657015179465621637324708889592560570247656753618930497634554609665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 250 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 250).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node250

namespace Node251
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 251 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204590034789694012342216926434885774577402029643768808169351705671444718244016737078597897589255988617476552557098577989876972754148753539909317361665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 251 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 251).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node251

namespace Node252
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 252 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[0]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204599400035347140835083958047246802047742939451799864006788567369617617846609082556849271085100874481297905130846687205192365401615541129803066507265 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 252 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 252).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node252

namespace Node253
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 253 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[0]], [[1, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (818350773913122920876000674127182070839267208767044176839383288658406209167173389079820921932320988789882407301176411685916945179819778588841575972865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 253 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 253).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node253

namespace Node254
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 254 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[0, 3], [2]], [[0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (15608980922093138341373881351391200270068807714525925774680264490960126949309540250361473546873478105076204678178950922822527366599400779793039365 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 254 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 254).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node254

namespace Node255
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 255 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834370125682169483275645324887558334434591839660707837291041070231388165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 255 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 255).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node255

namespace Node256
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 256 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [0]], [[0, 1], [0]], [[2], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 256 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 256).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node256

namespace Node257
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 257 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[2], [0]], [[0, 3]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (238174147370805943929655171987780765839672969276986783948063056854351305927546414749532347887752432895245236118487667693422308370358657679365 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 257 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 257).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node257

namespace Node258
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 258 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204599400178247268225221750763696609297564070928397523724816510846154344559299628723279541402327930490033329550528235442513669133556100911376074276865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 258 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 258).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node258

namespace Node259
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 259 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (818350773770222793485862881410732263589446077290446517121550897651658174660044760767184463037629833144202007977469628288949800693699515367037830692865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 259 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 259).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node259

namespace Node260
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 260 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [[1]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204590034932598500764700492792678877770070489147572589735348217602615023233620596294669547952899450394404245095097684779943894981765503227364143857665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 260 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 260).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node260

namespace Node261
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 261 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 2], [0]], [[1, 2], [0]], [[1, 2], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1125917086777345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 261 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 261).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node261

namespace Node262
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 262 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[0]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766954904976454179975506043398033716755045979863409803625819418625572865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 262 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 262).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node262

namespace Node263
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 263 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [0]], [[0, 1], [0]], [[0]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (134801790216449850488195388836956883261935375048938060500659507036165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 263 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 263).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node263

namespace Node264
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 6, rootOne ^ 2, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 264 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0]], [[1, 3], [0, 3]], [[0, 3]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 264 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 264).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node264

namespace Node265
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 6, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 265 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1]], [[0, 1]], [[0, 1]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766874026370581146047022189530989787667875443218163852436616028019032065 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 265 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 265).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node265

namespace Node266
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 266 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[1, 3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067496100545735587003645991222272547677715595663377443617001788500148225 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 266 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 266).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node266

namespace Node267
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 6 * root 9, root 5 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 267 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0, 1]], [[1, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1125917086777345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 267 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 267).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node267

namespace Node268
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 268 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1125917086777345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 268 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 268).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node268

namespace Node269
private def gen : Fin 7 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 269 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 3], [0]], [[0, 3], [0, 1]], [], [], [[0, 3], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (72339069014638849 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 269 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 269).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node269

namespace Node270
private def gen : Fin 7 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 270 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 2]], [[0, 1], [0]], [], [], [[1, 2]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (257 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 270 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 270).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node270

namespace Node272
private def gen : Fin 7 → SylowModel :=
  ![root 3, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 272 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[1, 2], [0, 1], [0]], [[0, 3], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1329227996094400882725152133300092929 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 272 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 272).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node272

namespace Node273
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 273 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 2], [0, 1]], [[1]], [], [], [], [[0, 2], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (0)))
private def sample (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 273 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 273).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node273

namespace Node274
private def gen : Fin 7 → SylowModel :=
  ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 274 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3]], [[2, 3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (799167629066964724696687218788402114860508536205664565996941247859437214107773199953673757765108725207992751497596175565865689707429602260187873281 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 274 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 274).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node274

namespace Node275
private def gen : Fin 7 → SylowModel :=
  ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 6 * root 7, root 5 * root 8, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 275 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[1, 4], [1, 2]], [], [[2, 3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3121748551042830999000168101067135880835484977063825916587248398968560702991091062305618710416431250157986032162838813568398059678427458389934081 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 275 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 275).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node275

namespace Node276
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 7, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 276 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 0 * root 2 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [], [[0]], [], [[0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (0)))
private def sample (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 276 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 276).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node276

namespace Node277
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 277 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [0, 1], [0, 1], [0]], [], [[0, 3], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (6434127454266934503936678062498564891385309149809387713332225 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 277 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 277).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node277

namespace Node278
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 278 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 3 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2]], [], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1025 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 278 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 278).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node278

namespace Node280
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 280 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[1, 2], [0, 1]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (26959946673525821244691948700878966576663740805436619760089834717185 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 280 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 280).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node280

namespace Node282
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 282 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[0, 3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3196670516267858898786748875153608459442034144822658263987764991437748856431092718934855010777210306286378540410568556117475866763828506060069535745 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 282 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 282).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node282

namespace Node283
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 283 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[0]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3199792264073892037339598246748556695766699017384953843679723394413892011996026787763264713258193220727189198894747224321246247440041852432862413825 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 283 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 283).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node283

namespace Node284
private def gen : Fin 7 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 9, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 284 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [1], [0]], [[1]], [[0, 3], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (188978068316857791553068711661943743527694660834079471883960995584093016803763282011107320770179163292397690339254083625392616007312344065 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 284 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 284).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node284

namespace Node285
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 285 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 5 * root 6 * root 7
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 2], [0, 1]], [[0, 2]], [], [], [[0, 2]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (285212689 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 285 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 285).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node285

namespace Node289
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 289 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 3]], [], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (2146051184422996578563097280106988998987750660984209265489508053194062326691789690616553342370806335534614635385459083587460397537951375090205903024431422736918283400714309069175538994201478152091518611766059276788602810828808580710046572603993201185942806136862665648593212866265636814329528430845854484805014451519002312644316532154666980238047272225652512979294092860576918467190713111198870438038522528876912424920368342658374105536151915221772796251769327318384675352133119125920373406499690648511872179480233653940925112610176108176129589801464097055478476057011989845192556908859619276732108402724418252439569 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (x.left.b7.val + 2 * (x.left.b8.val + 2 * (0)))))))))))
private def sample (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6, b7, b8] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 289 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 289).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node289

namespace Node290
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 6, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 290 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 3]], [], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (116337667820825142764365614319712687436089156966619448617163703191444083440719788613124722650230103816150015599412802844635760985264062628583036976453097864993524920036421179645653008237659666282153778936610536700743501113423206646638554922028162012440293736762425928619554457689543818970359989280103065628288498439483517572003097102262584963051614110601309394677886558898192084927461398362426432218058411833563707740232251645453413827064953329562934774787820520056983426877795381798692061160834914573378500569301807246558509263747028417065227476880398376574775876897018352187015978772570730135569 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (x.left.b7.val + 2 * (x.left.b8.val + 2 * (0)))))))))))
private def sample (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6, b7, b8] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 290 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 290).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node290

namespace Node292
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 292 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1]], [[1], [0]], [], [[0, 2], [0]], [[0, 2], [0]], [[0, 2], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (285212689 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 292 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 292).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node292

namespace Node293
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 293 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 3]], [[0, 3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (414928933294867758800497834487321433890554770745641362081823155470674617810104379786068694847923269202585572867008553161097838440727344839857110151221712048502323251979217055280672238772224469922015774505121193315002913398216087544905441481607760285530333672577101336228623129417352311687690423015107826992459057145526844771726298302268087694953059814975753436961911606136746937136299707738782820915266028295722494484782369497163451570562076819511282737001916194950698471552240684947473636382646345342825654421365481791027904532666231322035434589613243013144345776201634921180041489 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (x.left.b7.val + 2 * (x.left.b8.val + 2 * (0)))))))))))
private def sample (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6, b7, b8] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 293 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 293).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node293

namespace Node294
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 294 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 3]], [[0, 3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (454444014925099822101458185277261332575431435667995666188224654378733871397787995046124199386376444837275953238869023929044496391291491766972859011372204429826601329511453941026675629264280949711681292922103057271988197196711705078946267636536627843354407444530168862254555311194410536827309006762383224599080559996374702755838101514679784989200866874117824692022130956727922822221724349327742848078640562266783846138786840358087691132012223875075848559824567081162903819134706045790369639025579241280550249721672493892091682093874416517660754239182646947330348160181344403729767176999085801489 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (x.left.b7.val + 2 * (x.left.b8.val + 2 * (0)))))))))))
private def sample (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 9 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6, b7, b8] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 294 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 294).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node294

/-- The certified indices in batch F. -/
@[expose] public def indicesF : List (Fin 600) :=
  [248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 272, 273, 274, 275, 276, 277, 278, 280, 282, 283, 284, 285, 289, 290, 292, 293, 294]

/-- Every node listed in batch F has an outside Frattini normalizer witness. -/
public theorem witnessesF (i : Fin 600) (hi : i ∈ indicesF) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  simp only [indicesF, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Node248.witness
  · exact Node249.witness
  · exact Node250.witness
  · exact Node251.witness
  · exact Node252.witness
  · exact Node253.witness
  · exact Node254.witness
  · exact Node255.witness
  · exact Node256.witness
  · exact Node257.witness
  · exact Node258.witness
  · exact Node259.witness
  · exact Node260.witness
  · exact Node261.witness
  · exact Node262.witness
  · exact Node263.witness
  · exact Node264.witness
  · exact Node265.witness
  · exact Node266.witness
  · exact Node267.witness
  · exact Node268.witness
  · exact Node269.witness
  · exact Node270.witness
  · exact Node272.witness
  · exact Node273.witness
  · exact Node274.witness
  · exact Node275.witness
  · exact Node276.witness
  · exact Node277.witness
  · exact Node278.witness
  · exact Node280.witness
  · exact Node282.witness
  · exact Node283.witness
  · exact Node284.witness
  · exact Node285.witness
  · exact Node289.witness
  · exact Node290.witness
  · exact Node292.witness
  · exact Node293.witness
  · exact Node294.witness
end ReeTwo.SylowModel.SmallEvenLower
