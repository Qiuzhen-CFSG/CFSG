module

public import Theory.GroupTheory.FinitePredicateSeparation
public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Lower small even node witnesses, batch E

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

namespace Node206
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 206 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0, 3], [0, 2], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17179869185 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 206 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 206).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node206

namespace Node207
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 207 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[2]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (281492156841985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 207 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 207).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node207

namespace Node208
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 208 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[2]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (281492156841985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 208 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 208).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node208

namespace Node209
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 209 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2]], [], [], [[2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (281492156841985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 209 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 209).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node209

namespace Node210
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 210 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1, 4], [0]], [], [], [[0, 1]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (0))))
private def sample (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 210 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 210).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node210

namespace Node211
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 3 * root 5 * root 6 * root 7, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 211 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0]], [[0]], [[0, 4], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (79228162809412242841616252929 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 211 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 211).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node211

namespace Node212
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 212 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3], [0]], [], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235325948802345046899913040398051563744573439477497449511976603484165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 212 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 212).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node212

namespace Node213
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 213 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961880439531430797541360145858565 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 213 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 213).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node213

namespace Node214
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 214 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 214 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 214).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node214

namespace Node215
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 215 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 2], [3]], [], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834370125682169483275645324887558334434591839660707837291041070231388165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 215 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 215).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node215

namespace Node216
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 216 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (134799733367139186555125111348271356082270045062193124451270430556165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 216 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 216).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node216

namespace Node217
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 217 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766954904976454179975506043398033716755045979863409803625819418625572865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 217 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 217).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node217

namespace Node218
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 218 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067496100545735587003645991222272547677715595663377443617001788500148225 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 218 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 218).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node218

namespace Node219
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 219 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (262145 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 219 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 219).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node219

namespace Node220
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 220 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766874025136433897038258796289737547032537620130671599720901962448830465 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 220 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 220).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node220

namespace Node221
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 221 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[3]], [[3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067415220705715303491712916155463584879643361900058986220855842329329665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 221 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 221).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node221

namespace Node222
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 222 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 2], [3]], [], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834370123625257401594373002818804600042362134514887416098184294281052165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 222 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 222).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node222

namespace Node223
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 223 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (134801790216449850488195388836956883261935375048938060500659507036165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 223 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 223).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node223

namespace Node224
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 224 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 224 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 224).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node224

namespace Node225
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 225 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2], [0]], [], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235323891953033425171744738102138591780052988874675584761902305116165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 225 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 225).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node225

namespace Node226
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 226 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (2056912082639096650126307579921340514402622254579491854069596165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 226 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 226).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node226

namespace Node227
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 227 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766874026370581146047022189530989787667875443218163852436616028019032065 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 227 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 227).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node227

namespace Node228
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 228 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067415219471605717093353073988970373563335562702066939259226208883441665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 228 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 228).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node228

namespace Node229
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 229 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1125917086777345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 229 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 229).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node229

namespace Node230
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 230 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766954906210563766948542944379411264538224692133771496744669463204593665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 230 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 230).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node230

namespace Node232
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 232 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3], [0, 2]], [[2, 3], [0, 2]], [[0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (55453393895327546582002872501113600410109212700133178484411890190832028120305405100980739872953913316758910194604049619624510095365 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 232 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 232).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node232

namespace Node233
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 233 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204586913041142969522351928009830941403688995063297907927550878526516676578105548283595990087996823820223542509453348844209104514178678477666557886465 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 233 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 233).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node233

namespace Node234
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 234 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0, 1], [0]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (262145 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 234 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 234).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node234

namespace Node235
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 235 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235325948802345046899913040398051563744573439477497449511976603484165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 235 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 235).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node235

namespace Node236
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 236 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [0]], [[0, 1], [0]], [[0, 2], [0]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 236 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 236).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node236

namespace Node237
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 237 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204586913184045277428662607554699146259194488800482994204714002523508566182697131954559058478680540728039485026872503764294194028430380474286592753665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 237 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 237).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node237

namespace Node239
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 239 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3], [0]], [[2, 3], [0]], [[0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961880439531430797541360145858565 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 239 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 239).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node239

namespace Node240
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 240 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (2404944301298205796125980932335003512929820534445907101397709463293631425262472004110191862391779897792054493185 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 240 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 240).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node240

namespace Node241
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 241 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (262145 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 241 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 241).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node241

namespace Node242
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 242 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3], [0]], [[3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961880439531430797541360145858565 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 242 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 242).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node242

namespace Node243
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 243 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (2404916778894861776109501821012264579839250944821646666609619410878142728568953385277302603075361080784055435265 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 243 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 243).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node243

namespace Node244
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 244 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1125917086777345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 244 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 244).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node244

namespace Node245
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 245 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 2], [2]], [[1, 2], [2]], [[0, 3]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 245 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 245).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node245

namespace Node246
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 246 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0]], [[1, 3], [0]], [[0]], [[2, 3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 246 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 246).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node246

namespace Node247
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 247 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [], [[1, 3], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3121748551042830955846434448392195761201383452951666030174136300151313462210842328337978796686215117710871654844807534638257569959263432934948865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 247 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 247).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node247

/-- The certified indices in batch E. -/
@[expose] public def indicesE : List (Fin 600) :=
  [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 232, 233, 234, 235, 236, 237, 239, 240, 241, 242, 243, 244, 245, 246, 247]

/-- Every node listed in batch E has an outside Frattini normalizer witness. -/
public theorem witnessesE (i : Fin 600) (hi : i ∈ indicesE) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  simp only [indicesE, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Node206.witness
  · exact Node207.witness
  · exact Node208.witness
  · exact Node209.witness
  · exact Node210.witness
  · exact Node211.witness
  · exact Node212.witness
  · exact Node213.witness
  · exact Node214.witness
  · exact Node215.witness
  · exact Node216.witness
  · exact Node217.witness
  · exact Node218.witness
  · exact Node219.witness
  · exact Node220.witness
  · exact Node221.witness
  · exact Node222.witness
  · exact Node223.witness
  · exact Node224.witness
  · exact Node225.witness
  · exact Node226.witness
  · exact Node227.witness
  · exact Node228.witness
  · exact Node229.witness
  · exact Node230.witness
  · exact Node232.witness
  · exact Node233.witness
  · exact Node234.witness
  · exact Node235.witness
  · exact Node236.witness
  · exact Node237.witness
  · exact Node239.witness
  · exact Node240.witness
  · exact Node241.witness
  · exact Node242.witness
  · exact Node243.witness
  · exact Node244.witness
  · exact Node245.witness
  · exact Node246.witness
  · exact Node247.witness
end ReeTwo.SylowModel.SmallEvenLower
