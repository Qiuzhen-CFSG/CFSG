module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!
# Frattini witnesses for upper node block 10

Explicit projected orbits separate the proposed witnesses from the node
subgroups. Products of squares certify all generator displacements. The
coordinate bridge transfers these kernel-checked equations to the unchanged
root-word nodes.

Source: Shinoda (1975), (2.3), pp. 81–82, and the fixed node words in
`SmallEvenDescentNodes`. Certificate suggestions are verified here in Lean.
-/

namespace ReeTwo.SylowModel.UpperCertificate
set_option maxRecDepth 10000

namespace Node500
private def roots : Fin 6 → SylowModel := ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 5 * root 8, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 500 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 500 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [1]], [[1, 2], [1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 500).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node500
namespace Node501
private def roots : Fin 6 → SylowModel := ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 5 * root 8, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 501 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 501 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 501).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node501
namespace Node502
private def roots : Fin 6 → SylowModel := ![root 2 * root 7, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8, root 5 * root 8, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 502 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 502 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 502).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node502
namespace Node503
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 503 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 503 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 503).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node503
namespace Node504
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 8, root 4 * root 5 * root 8 * root 9, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 504 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 504 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 504).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node504
namespace Node505
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 4 * root 5 * root 8 * root 9, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 505 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 505 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[3]], [[0, 3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 505).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node505
namespace Node506
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 4 * root 5 * root 8 * root 9, root 8, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 506 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 506 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[3]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 506).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node506
namespace Node507
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 507 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![6, 7, 4, 5, 2, 3, 0, 1, 15, 14, 13, 12, 11, 10, 9, 8], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 507 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 507).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node507
namespace Node508
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 6, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 508 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![8, 9, 10, 11, 13, 12, 15, 14, 0, 1, 2, 3, 5, 4, 7, 6], ![13, 12, 15, 14, 10, 11, 8, 9, 4, 5, 6, 7, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 508 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 508).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node508
namespace Node509
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 509 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 26, 27, 24, 25, 30, 31, 28, 29, 1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13], ![26, 27, 24, 25, 30, 31, 28, 29, 20, 21, 22, 23, 16, 17, 18, 19, 9, 8, 11, 10, 13, 12, 15, 14, 7, 6, 5, 4, 3, 2, 1, 0], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 509 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 3], [1]], [[1, 3], [1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 509).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node509
namespace Node510
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 510 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 26, 27, 24, 25, 30, 31, 28, 29, 1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13], ![26, 27, 24, 25, 30, 31, 28, 29, 20, 21, 22, 23, 16, 17, 18, 19, 9, 8, 11, 10, 13, 12, 15, 14, 7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 510 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 510).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node510
namespace Node511
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 6, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 511 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![8, 9, 10, 11, 13, 12, 15, 14, 0, 1, 2, 3, 5, 4, 7, 6], ![13, 12, 15, 14, 10, 11, 8, 9, 4, 5, 6, 7, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 511 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 511).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node511
namespace Node512
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 512 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 26, 27, 24, 25, 30, 31, 28, 29, 1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13], ![27, 26, 25, 24, 31, 30, 29, 28, 21, 20, 23, 22, 17, 16, 19, 18, 8, 9, 10, 11, 12, 13, 14, 15, 6, 7, 4, 5, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 512 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 512).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node512
namespace Node513
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 513 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![19, 18, 17, 16, 23, 22, 21, 20, 24, 25, 26, 27, 28, 29, 30, 31, 3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15], ![26, 27, 24, 25, 30, 31, 28, 29, 20, 21, 22, 23, 16, 17, 18, 19, 9, 8, 11, 10, 13, 12, 15, 14, 7, 6, 5, 4, 3, 2, 1, 0], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 513 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 513).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node513
namespace Node514
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 514 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 24, 25, 26, 27, 28, 29, 30, 31, 2, 3, 0, 1, 6, 7, 4, 5, 11, 10, 9, 8, 15, 14, 13, 12], ![26, 27, 24, 25, 30, 31, 28, 29, 21, 20, 23, 22, 17, 16, 19, 18, 8, 9, 10, 11, 12, 13, 14, 15, 7, 6, 5, 4, 3, 2, 1, 0], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 514 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 3], [1]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 514).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node514
namespace Node515
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 515 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 515 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[1], [0]], [[0, 1], [1]], [[0, 1], [1]], [[0, 1], [1]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 515).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node515
namespace Node516
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 516 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 516 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1, 2], [0]], [[1, 2], [1]], [[1, 2], [1]], [[1, 2], [1]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 516).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node516
namespace Node517
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 517 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![8, 9, 10, 11, 12, 13, 14, 15, 1, 0, 3, 2, 5, 4, 7, 6], ![13, 12, 15, 14, 10, 11, 8, 9, 4, 5, 6, 7, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 517 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 517).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node517
namespace Node518
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 7 * root 8 * root 9, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 518 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 24, 25, 26, 27, 28, 29, 30, 31, 2, 3, 0, 1, 6, 7, 4, 5, 11, 10, 9, 8, 15, 14, 13, 12], ![26, 27, 24, 25, 30, 31, 28, 29, 21, 20, 23, 22, 17, 16, 19, 18, 8, 9, 10, 11, 12, 13, 14, 15, 7, 6, 5, 4, 3, 2, 1, 0], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18, 29, 28, 31, 30, 25, 24, 27, 26], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 518 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 518).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node518
namespace Node519
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 8, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 519 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 519 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 519).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node519
namespace Node520
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 520 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 520 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[1], [0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 520).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node520
namespace Node521
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 521 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 521 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1], [0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 521).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node521
namespace Node522
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 522 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![23, 22, 21, 20, 19, 18, 17, 16, 28, 29, 30, 31, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12], ![15, 14, 13, 12, 11, 10, 9, 8, 3, 2, 1, 0, 7, 6, 5, 4, 24, 25, 26, 27, 28, 29, 30, 31, 20, 21, 22, 23, 16, 17, 18, 19], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 522 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 522).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node522
namespace Node523
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 523 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![11, 10, 9, 8, 14, 15, 12, 13, 0, 1, 2, 3, 5, 4, 7, 6], ![7, 6, 5, 4, 1, 0, 3, 2, 12, 13, 14, 15, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 523 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 523).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node523
namespace Node524
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 524 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![23, 22, 21, 20, 19, 18, 17, 16, 28, 29, 30, 31, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12], ![15, 14, 13, 12, 11, 10, 9, 8, 3, 2, 1, 0, 7, 6, 5, 4, 24, 25, 26, 27, 28, 29, 30, 31, 20, 21, 22, 23, 16, 17, 18, 19], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 524 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 524).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node524
namespace Node525
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 525 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![23, 22, 21, 20, 19, 18, 17, 16, 28, 29, 30, 31, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 11, 10, 9, 8, 15, 14, 13, 12], ![15, 14, 13, 12, 11, 10, 9, 8, 3, 2, 1, 0, 7, 6, 5, 4, 24, 25, 26, 27, 28, 29, 30, 31, 20, 21, 22, 23, 16, 17, 18, 19], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 525 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 525).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node525
namespace Node526
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 526 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 16 → Fin 16 := ![![11, 10, 9, 8, 14, 15, 12, 13, 0, 1, 2, 3, 5, 4, 7, 6], ![7, 6, 5, 4, 1, 0, 3, 2, 12, 13, 14, 15, 10, 11, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 526 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 526).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node526
namespace Node527
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 527 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 527 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 527).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node527
namespace Node528
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 528 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 528 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[2]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 528).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node528
namespace Node529
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 529 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 529 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 529).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node529
namespace Node530
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 530 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 530 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1], [0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 530).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node530
namespace Node531
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 531 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 531 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 531).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node531
namespace Node532
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 532 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 532 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[2]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 532).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node532
namespace Node533
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 533 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 533 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 533).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node533
namespace Node534
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 534 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 534 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[1], [0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 534).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node534
namespace Node535
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 535 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 535 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[0, 1], [2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 535).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node535
namespace Node536
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 536 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 536 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 536).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node536
namespace Node537
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 537 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 537 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 537).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node537
namespace Node538
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 538 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 538 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [1]], [[0, 1], [2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 538).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node538
namespace Node539
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 539 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 539 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 539).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node539
namespace Node540
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 540 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 540 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 540).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node540
namespace Node541
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 541 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 541 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 541).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node541
namespace Node542
private def roots : Fin 6 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 542 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 542 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[1], [0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 542).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node542
namespace Node544
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 8 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 544 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![3, 2, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 544 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 544).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node544
namespace Node545
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 545 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1)]
private def next : Fin 5 → Fin 16 → Fin 16 := ![![15, 14, 12, 13, 11, 10, 8, 9, 3, 2, 0, 1, 6, 7, 5, 4], ![7, 6, 5, 4, 2, 3, 0, 1, 14, 15, 12, 13, 11, 10, 9, 8], ![4, 5, 6, 7, 1, 0, 3, 2, 13, 12, 15, 14, 8, 9, 10, 11], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 545 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 545).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node545
namespace Node547
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 547 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 547 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 547).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node547
namespace Node549
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 549 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 549 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 549).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node549

/-- Checked witnesses at indices 500 through 549, excluding the prescribed survivors. -/
@[expose] public def block10 :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  [⟨500, by exact Node500.witness⟩,
  ⟨501, by exact Node501.witness⟩,
  ⟨502, by exact Node502.witness⟩,
  ⟨503, by exact Node503.witness⟩,
  ⟨504, by exact Node504.witness⟩,
  ⟨505, by exact Node505.witness⟩,
  ⟨506, by exact Node506.witness⟩,
  ⟨507, by exact Node507.witness⟩,
  ⟨508, by exact Node508.witness⟩,
  ⟨509, by exact Node509.witness⟩,
  ⟨510, by exact Node510.witness⟩,
  ⟨511, by exact Node511.witness⟩,
  ⟨512, by exact Node512.witness⟩,
  ⟨513, by exact Node513.witness⟩,
  ⟨514, by exact Node514.witness⟩,
  ⟨515, by exact Node515.witness⟩,
  ⟨516, by exact Node516.witness⟩,
  ⟨517, by exact Node517.witness⟩,
  ⟨518, by exact Node518.witness⟩,
  ⟨519, by exact Node519.witness⟩,
  ⟨520, by exact Node520.witness⟩,
  ⟨521, by exact Node521.witness⟩,
  ⟨522, by exact Node522.witness⟩,
  ⟨523, by exact Node523.witness⟩,
  ⟨524, by exact Node524.witness⟩,
  ⟨525, by exact Node525.witness⟩,
  ⟨526, by exact Node526.witness⟩,
  ⟨527, by exact Node527.witness⟩,
  ⟨528, by exact Node528.witness⟩,
  ⟨529, by exact Node529.witness⟩,
  ⟨530, by exact Node530.witness⟩,
  ⟨531, by exact Node531.witness⟩,
  ⟨532, by exact Node532.witness⟩,
  ⟨533, by exact Node533.witness⟩,
  ⟨534, by exact Node534.witness⟩,
  ⟨535, by exact Node535.witness⟩,
  ⟨536, by exact Node536.witness⟩,
  ⟨537, by exact Node537.witness⟩,
  ⟨538, by exact Node538.witness⟩,
  ⟨539, by exact Node539.witness⟩,
  ⟨540, by exact Node540.witness⟩,
  ⟨541, by exact Node541.witness⟩,
  ⟨542, by exact Node542.witness⟩,
  ⟨544, by exact Node544.witness⟩,
  ⟨545, by exact Node545.witness⟩,
  ⟨547, by exact Node547.witness⟩,
  ⟨549, by exact Node549.witness⟩]

end ReeTwo.SylowModel.UpperCertificate
