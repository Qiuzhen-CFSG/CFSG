module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!
# Frattini witnesses for upper node block 9

Projected orbits and the parity character separate the proposed witnesses from the node
subgroups. Products of squares certify all generator displacements. The
coordinate bridge transfers these kernel-checked equations to the unchanged
root-word nodes.

Source: Shinoda (1975), (2.3), pp. 81–82, and the fixed node words in
`SmallEvenDescentNodes`. Certificate suggestions are verified here in Lean.
-/

namespace ReeTwo.SylowModel.UpperCertificate
set_option maxRecDepth 10000

namespace Node450
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 450 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 450 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 450).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node450
namespace Node451
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 451 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 451 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 451).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node451
namespace Node452
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 452 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 452 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 2], [0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 452).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node452
namespace Node453
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 453 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 453 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 453).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node453
namespace Node454
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 454 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 454 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 454).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node454
namespace Node455
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 455 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 455 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [2], [0]], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 455).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node455
namespace Node456
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 456 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 456 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 456).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node456
namespace Node457
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 457 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 457 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 457).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node457
namespace Node458
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 458 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 458 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 458).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node458
namespace Node459
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 459 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 459 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 459).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node459
namespace Node460
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 460 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 460 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [1], [0]], [[2], [1], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 460).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node460
namespace Node461
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 461 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 2 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 461 := by
  rw [generated]
  exact outside_of_projected_orbit gen 2 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[0, 1], [1], [0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 461).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node461
namespace Node463
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 463 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 463 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 463).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node463
namespace Node464
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 464 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne
private theorem outside : g ∉ smallEvenDescentNode 464 := by
  have hle : smallEvenDescentNode 464 ≤ character.ker := by
    rw [generated, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (by decide +kernel : ∀ i, character (encode (gen i)) = 1) i
  intro h
  exact (by decide +kernel : character g ≠ 1) (hle h)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [], [[0, 2], [0]], [[0, 2], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, encode (squareWord gen (squares i)) =
    (encode (gen i))⁻¹ * (g * encode (gen i) * g⁻¹) := by decide +kernel
private theorem witness : (smallEvenDescentNode 464).HasFrattiniNormalizerWitness := by
  apply Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated g outside squares
  intro i
  rw [← encode_squareWord]
  exact checked i
end Node464
namespace Node465
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 465 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 465 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 465).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node465
namespace Node466
private def roots : Fin 6 → SylowModel := ![root 3 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 466 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 466 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [[0, 1], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 466).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node466
namespace Node467
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 467 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 467 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 467).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node467
namespace Node468
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 468 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 468 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [[0, 1], [0]], [[2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 468).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node468
namespace Node469
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 469 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 469 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [0]], [[1, 2], [0]], [[1, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 469).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node469
namespace Node470
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 470 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 470 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 470).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node470
namespace Node471
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 471 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 471 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 471).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node471
namespace Node472
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 472 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 472 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 472).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node472
namespace Node473
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 473 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 473 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 473).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node473
namespace Node474
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 474 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 474 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 474).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node474
namespace Node475
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 475 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 475 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 475).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node475
namespace Node476
private def roots : Fin 6 → SylowModel := ![root 3 * root 5 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 476 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 476 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 476).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node476
namespace Node477
private def roots : Fin 6 → SylowModel := ![root 3 * root 5 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 477 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 477 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 477).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node477
namespace Node478
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 478 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 478 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 478).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node478
namespace Node479
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 479 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 479 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 479).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node479
namespace Node480
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 480 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 480 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 480).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node480
namespace Node481
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 481 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 481 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 481).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node481
namespace Node482
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 482 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 482 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 482).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node482
namespace Node483
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 483 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 483 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 483).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node483
namespace Node484
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 484 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 484 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 484).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node484
namespace Node485
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 485 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 485 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 485).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node485
namespace Node486
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 486 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 486 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 486).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node486
namespace Node487
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 487 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 487 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 487).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node487
namespace Node488
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 488 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 488 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 488).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node488
namespace Node489
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 489 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 489 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 489).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node489
namespace Node490
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 490 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 490 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 490).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node490
namespace Node491
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 491 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 491 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 491).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node491
namespace Node492
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 492 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 492 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[1, 2], [2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 492).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node492
namespace Node493
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 493 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 493 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [0, 2]], [[1, 2], [0]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 493).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node493
namespace Node494
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 494 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 494 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [[1, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 494).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node494
namespace Node495
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 495 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 495 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [1], [0]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 495).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node495
namespace Node496
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 496 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 496 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [2]], [[1, 2], [1]], [[1, 2], [2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 496).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node496
namespace Node497
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 497 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 497 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 497).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node497
namespace Node498
private def roots : Fin 6 → SylowModel := ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 8, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 498 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 498 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 3], [0]], [], [], [], [[0, 3], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 498).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node498
namespace Node499
private def roots : Fin 6 → SylowModel := ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 8, root 5 * root 8, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 499 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 499 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 499).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node499

/-- Checked witnesses at indices 450 through 499, excluding the prescribed survivors. -/
@[expose] public def block9 :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  [⟨450, by exact Node450.witness⟩,
  ⟨451, by exact Node451.witness⟩,
  ⟨452, by exact Node452.witness⟩,
  ⟨453, by exact Node453.witness⟩,
  ⟨454, by exact Node454.witness⟩,
  ⟨455, by exact Node455.witness⟩,
  ⟨456, by exact Node456.witness⟩,
  ⟨457, by exact Node457.witness⟩,
  ⟨458, by exact Node458.witness⟩,
  ⟨459, by exact Node459.witness⟩,
  ⟨460, by exact Node460.witness⟩,
  ⟨461, by exact Node461.witness⟩,
  ⟨463, by exact Node463.witness⟩,
  ⟨464, by exact Node464.witness⟩,
  ⟨465, by exact Node465.witness⟩,
  ⟨466, by exact Node466.witness⟩,
  ⟨467, by exact Node467.witness⟩,
  ⟨468, by exact Node468.witness⟩,
  ⟨469, by exact Node469.witness⟩,
  ⟨470, by exact Node470.witness⟩,
  ⟨471, by exact Node471.witness⟩,
  ⟨472, by exact Node472.witness⟩,
  ⟨473, by exact Node473.witness⟩,
  ⟨474, by exact Node474.witness⟩,
  ⟨475, by exact Node475.witness⟩,
  ⟨476, by exact Node476.witness⟩,
  ⟨477, by exact Node477.witness⟩,
  ⟨478, by exact Node478.witness⟩,
  ⟨479, by exact Node479.witness⟩,
  ⟨480, by exact Node480.witness⟩,
  ⟨481, by exact Node481.witness⟩,
  ⟨482, by exact Node482.witness⟩,
  ⟨483, by exact Node483.witness⟩,
  ⟨484, by exact Node484.witness⟩,
  ⟨485, by exact Node485.witness⟩,
  ⟨486, by exact Node486.witness⟩,
  ⟨487, by exact Node487.witness⟩,
  ⟨488, by exact Node488.witness⟩,
  ⟨489, by exact Node489.witness⟩,
  ⟨490, by exact Node490.witness⟩,
  ⟨491, by exact Node491.witness⟩,
  ⟨492, by exact Node492.witness⟩,
  ⟨493, by exact Node493.witness⟩,
  ⟨494, by exact Node494.witness⟩,
  ⟨495, by exact Node495.witness⟩,
  ⟨496, by exact Node496.witness⟩,
  ⟨497, by exact Node497.witness⟩,
  ⟨498, by exact Node498.witness⟩,
  ⟨499, by exact Node499.witness⟩]

end ReeTwo.SylowModel.UpperCertificate
