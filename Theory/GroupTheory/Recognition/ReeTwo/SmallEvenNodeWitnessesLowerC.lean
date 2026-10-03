module

public import Theory.GroupTheory.FinitePredicateSeparation
public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Lower small even node witnesses, batch C

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

namespace Node110
private def gen : Fin 8 → SylowModel :=
  ![root 3 * root 6 * root 8, rootOne ^ 2 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 110 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1]], [[1]], [[2, 4], [1, 2], [0]], [[1, 3], [1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (802289378178400212084446565880701913280754037136189418219694772003249400707469822759357466348761878034026868732510226899258278755293775720504885505 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 110 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 110).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node110

namespace Node111
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 111 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 2], [0, 1], [2], [1]], [], [[0, 4], [0, 2]], [], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1224997790343561233 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 111 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 111).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node111

namespace Node116
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 116 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2, 4], [1, 2], [1]], [[2, 4], [1, 2], [1]], [[0, 6], [0, 2]], [], [], [[0, 6]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17829889 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 116 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 116).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node116

namespace Node117
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 117 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3], [0, 2], [0, 1]], [[1, 3], [0, 1]], [[0, 6], [0, 2]], [], [], [[0, 6]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1157442765156581633 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 0, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 117 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 117).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node117

namespace Node118
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 118 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 2], [2]], [[2], [1]], [[0, 2], [0, 1]], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1224997790343561233 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 118 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 118).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node118

namespace Node121
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 121 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1]], [[1, 3], [0]], [[0, 2], [0]], [], [], [[0, 1]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1329248278213862633988909350472712193 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 121 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 121).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node121

namespace Node122
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 122 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 2], [2]], [[2]], [[0, 2], [0]], [], [], [[0, 3], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (21267668214969466839170931906489352193 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 122 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 122).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node122

namespace Node123
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 123 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2, 5], [1]], [[0, 4], [0, 1]], [[0, 4], [0, 2]], [], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (4369 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 123 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 123).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node123

namespace Node124
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 5 * root 6, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 124 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2]], [[1, 2]], [[0, 1], [2], [1]], [], [], [[0, 4]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (285212689 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 124 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 124).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node124

namespace Node125
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 125 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 2], [0]], [], [[0, 2], [0, 1]], [], [[0, 3], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (269484289 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 0, 1, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 125 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 125).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node125

namespace Node126
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 5 * root 6, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 126 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 2], [0]], [[0, 2], [2]], [[0, 1], [0]], [], [], [[0, 3], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17829889 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 0, 1, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 126 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 126).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node126

namespace Node127
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 127 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 2]], [[0, 2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (65 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (0)))
private def sample (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 127 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 127).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node127

namespace Node128
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 128 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0 * root 2 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 4], [0, 1]], [[0]], [[2]], [[0, 4], [0, 4], [0, 4], [0]], [[0, 4], [0, 4], [0, 4], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (18295959386849345 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 128 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 128).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node128

namespace Node130
private def gen : Fin 7 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 130 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0, 1], [2]], [[0, 4]], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3477977524128769716098734296716382454726780098679801516600217309017624322401161213876671913684432336429245556448017410209746668409957882610608817307665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 130 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 130).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node130

namespace Node131
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 131 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0, 3]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961484298718767240725648994467845 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 131 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 131).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node131

namespace Node132
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 132 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0, 4]], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3477977521699430481691444113838589190479910659140127589827313413037088714376941037826218849584053863469876802115589145871586364514218577290358448717841 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 132 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 132).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node132

namespace Node133
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 133 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0 * root 2 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0]], [[0, 1]], [[2]], [[0, 4], [0, 4], [0, 4], [0]], [[0, 4], [0, 4], [0, 4], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (13298149344578076346928583143362124117010511077700198468428575054156840853977984004447060220537983754355755933812895152637320862481323978773728256327745 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 133 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 133).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node133

namespace Node134
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 134 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 0
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1]], [[0, 3], [0]], [[2]], [[2]], [[0, 3], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (65 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (0)))
private def sample (v : Fin 1 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 134 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 134).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node134

namespace Node135
private def gen : Fin 7 → SylowModel :=
  ![root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 135 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1 : ℕ).testBit (x.right.toAdd.val + 4 * (0))
private def sample (_v : Fin 0 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 0 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 135 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 135).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node135

namespace Node137
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 137 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[0, 1], [1]], [[1, 2], [0, 1], [0]], [], [[2]], [[0, 3], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1407718486179845 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 137 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 137).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node137

namespace Node139
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 139 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204586913041142969511261418461093481795340828731210199636039364292873335693022746360209349515006110439975276649570850092651384520765625195931384152065 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 139 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 139).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node139

namespace Node140
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 140 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961484298718767240725648994467845 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 7 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
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
private theorem not_mem : g ∉ smallEvenDescentNode 140 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 140).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node140

namespace Node141
private def gen : Fin 7 → SylowModel :=
  ![root 0, root 0 * root 2 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 141 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0, 4]], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3477977520889650736889014052879324769064287512629282676358242706471789146425011201163077288448395751139197705766449501458991610187423194448513543962641 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 141 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 141).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node141

namespace Node143
private def gen : Fin 7 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 143 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (281492156841985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 143 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 143).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node143

namespace Node144
private def gen : Fin 7 → SylowModel :=
  ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 144 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1]], [[1]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204586913184045277417572605689198967927509619291947537307051841922043847684539776359587272068357542027742176005301375577226929401964810403315779108865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 144 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 144).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node144

namespace Node145
private def gen : Fin 7 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 145 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (27973577474460602098745814604961665481870226492701212717936017425 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 145 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 145).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node145

namespace Node146
private def gen : Fin 7 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 146 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 4]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3239118979209720243837057685662492586062417484184794229686896682923564492548715185347838600691014176629199209587895870233312986814131384352785 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 146 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 146).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node146

namespace Node147
private def gen : Fin 7 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 147 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0 * root 2 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3], [0, 1]], [[3]], [[0, 2], [0, 1]], [[0, 2]], [[0, 2]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (88269046677299025418813513534537745 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 147 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 147).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node147

namespace Node148
private def gen : Fin 7 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 148 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0 * root 2 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 2], [1, 2], [1, 2]], [[3]], [[1, 2], [1]], [[0, 4]], [[0, 4]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (30036400129206111077376659611375435158829129384791834613870639555907944465 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 148 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 148).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node148

namespace Node149
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 149 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2, 3]], [], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235325948802344567995056408304057334107615606514622650005857123696645 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 149 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 149).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node149

namespace Node150
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 150 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961484298718767240725648994467845 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 150 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 150).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node150

namespace Node151
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 151 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 151 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 151).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node151

namespace Node152
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 152 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[2]], [], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1022934565205714847556306246153827160439448099712109374547178033502770071951691192829535799019762493038063116287366995463322145350112119882817847951365 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 152 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 152).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node152

namespace Node153
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 153 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[3]], [[3]], [[0, 3], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235325948802344568002363916492413286494723021714288178866923147100165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 153 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 153).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node153

namespace Node154
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 154 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (846151640248531243774930640770105760580055752771786384383412532903435615532125405396178497637781888820869316274225423958671365 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 154 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 154).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node154

namespace Node155
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 155 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766847065189760468913604857288211496228731209053462656953090024243462145 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 155 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 155).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node155

namespace Node156
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 156 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067388260759041875654401891133193930613618887838140170198658149120999425 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 156 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 156).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node156

namespace Node157
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 157 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [], [[0]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (204586913041142969511261926152077630910479732281614149583140793550697536235585860867114725912099296405939195485784031497879220460266337493950989860865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 157 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 157).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node157

namespace Node158
private def gen : Fin 7 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 158 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[], [[3]], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (818347652164571878045045673844373927174148592108879774311447613652359579406595276023640636042550051427358715362756256879038694641760702103487810371585 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 158 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 158).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node158

namespace Node159
private def gen : Fin 7 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private theorem generated : smallEvenDescentNode 159 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 7 → List (List (Fin 7)) :=
  ![[[1, 3]], [[1, 3]], [[0, 3], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 7 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
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
private theorem not_mem : g ∉ smallEvenDescentNode 159 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 159).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node159

/-- The certified indices in batch C. -/
@[expose] public def indicesC : List (Fin 600) :=
  [110, 111, 116, 117, 118, 121, 122, 123, 124, 125, 126, 127, 128, 130, 131, 132, 133, 134, 135, 137, 139, 140, 141, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]

/-- Every node listed in batch C has an outside Frattini normalizer witness. -/
public theorem witnessesC (i : Fin 600) (hi : i ∈ indicesC) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  simp only [indicesC, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Node110.witness
  · exact Node111.witness
  · exact Node116.witness
  · exact Node117.witness
  · exact Node118.witness
  · exact Node121.witness
  · exact Node122.witness
  · exact Node123.witness
  · exact Node124.witness
  · exact Node125.witness
  · exact Node126.witness
  · exact Node127.witness
  · exact Node128.witness
  · exact Node130.witness
  · exact Node131.witness
  · exact Node132.witness
  · exact Node133.witness
  · exact Node134.witness
  · exact Node135.witness
  · exact Node137.witness
  · exact Node139.witness
  · exact Node140.witness
  · exact Node141.witness
  · exact Node143.witness
  · exact Node144.witness
  · exact Node145.witness
  · exact Node146.witness
  · exact Node147.witness
  · exact Node148.witness
  · exact Node149.witness
  · exact Node150.witness
  · exact Node151.witness
  · exact Node152.witness
  · exact Node153.witness
  · exact Node154.witness
  · exact Node155.witness
  · exact Node156.witness
  · exact Node157.witness
  · exact Node158.witness
  · exact Node159.witness
end ReeTwo.SylowModel.SmallEvenLower
