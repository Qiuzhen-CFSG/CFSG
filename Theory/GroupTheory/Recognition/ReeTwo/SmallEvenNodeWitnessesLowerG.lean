module

public import Theory.GroupTheory.FinitePredicateSeparation
public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Lower small even node witnesses, batch G

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

namespace Node295
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 295 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [1]], [[0, 1], [1], [0]], [], [[0, 2], [0]], [[0, 2], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (269484289 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 0, 1, 0, 0, 1⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 295 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 295).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node295

namespace Node296
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 6 * root 8, root 6 * root 7, root 7 * root 8, root 9]
private theorem generated : smallEvenDescentNode 296 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0]], [[1, 2], [0, 1]], [], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (75853011631093676245249 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 296 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 296).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node296

namespace Node297
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 297 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 0 * root 4 * root 6 * root 8 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 4]], [[0]], [], [], [[0, 1], [0]], [[0, 1], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (269484289 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 297 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 297).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node297

namespace Node298
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 298 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 0
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [[0, 4], [0]], [], [[0, 4], [0]], [[0, 4], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17829889 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 298 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 298).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node298

namespace Node299
private def gen : Fin 7 → SylowModel :=
  ![root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 299 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 3 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0, 1], [0]], [[0, 3], [0, 1]], [[0, 3], [0]], [[0, 3], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1152921573343100929 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 299 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 299).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node299

/-- The certified indices in batch G. -/
@[expose] public def indicesG : List (Fin 600) :=
  [295, 296, 297, 298, 299]

/-- Every node listed in batch G has an outside Frattini normalizer witness. -/
public theorem witnessesG (i : Fin 600) (hi : i ∈ indicesG) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  simp only [indicesG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl)
  · exact Node295.witness
  · exact Node296.witness
  · exact Node297.witness
  · exact Node298.witness
  · exact Node299.witness
end ReeTwo.SylowModel.SmallEvenLower
