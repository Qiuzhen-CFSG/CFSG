module

public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodes
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniCoordinates

/-!
# An outside Frattini witness for descent node twelve

The parity-quotient character `(t/2) + b₀` kills all nine node generators
and separates `rootOne²` from their closure. Four nontrivial generator
displacements are squares of explicit words; the other five vanish. The
square-word criterion supplies normalization and trivial Frattini action.

Source: direct calculation with the Shinoda (1975), (2.3), pp. 81–82 root
coordinates. All concrete equations are checked by kernel reduction.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 10000
private def planeCharacter : ParityQuotient →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (v.toAdd 0 + v.toAdd 1)
  map_one' := rfl
  map_mul' x y := by change (x.toAdd 0 + y.toAdd 0) + (x.toAdd 1 + y.toAdd 1) = (x.toAdd 0 + x.toAdd 1) + (y.toAdd 0 + y.toAdd 1); ring

private def upper : Subgroup SylowModel :=
  (planeCharacter.comp parityProjection).ker.map ParityKernel.subtype

private theorem mem_upper (x : SylowModel) : x ∈ upper ↔
    parity x.right = 1 ∧ ((x.right.toAdd.val / 2 : ℕ) : ZMod 2) + x.left.b0 = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(mem_parityKernel y).mp y.property, hy⟩
  · rintro ⟨hp, hc⟩
    exact ⟨⟨x, (mem_parityKernel x).mpr hp⟩, hc, rfl⟩

private def gen : Fin 9 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
    rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8,
    root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
    root 2 * root 3 * root 4 * root 9,
    root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]

private theorem generated : smallEvenDescentNode 12 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]
  rfl

private theorem outside : rootOne ^ 2 ∉ smallEvenDescentNode 12 := by
  have hle : smallEvenDescentNode 12 ≤ upper := by
    rw [generated, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change gen i ∈ upper
    rw [mem_upper]
    exact (by decide +kernel : ∀ i,
      parity (gen i).right = 1 ∧
        (((gen i).right.toAdd.val / 2 : ℕ) : ZMod 2) + (gen i).left.b0 = 0) i
  intro h
  have hh := (mem_upper _).mp (hle h)
  exact (by decide +kernel : ¬ (parity (rootOne ^ 2).right = 1 ∧
    (((rootOne ^ 2).right.toAdd.val / 2 : ℕ) : ZMod 2) + (rootOne ^ 2).left.b0 = 0)) hh

private def squares : Fin 9 → List (List (Fin 9)) :=
  ![[[0, 3]], [[0, 3]], [], [[3]], [], [[0, 1]], [], [], []]

set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) =
      (gen i)⁻¹ * (rootOne ^ 2 * gen i * (rootOne ^ 2)⁻¹) := by decide +kernel

/-- Descent node twelve has an outside Frattini witness. -/
public theorem smallEvenDescentNode_twelve_witness :
    (smallEvenDescentNode 12).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated _ outside squares checked
end ReeTwo.SylowModel
