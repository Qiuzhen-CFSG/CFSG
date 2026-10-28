module

public import Theory.Representation.G2OrthogonalCover.HyperplaneCubicMover
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank.CubicWitness
import all Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
import all Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank.CubicWitness
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Derived actors for both cover-hyperplane component arguments

The norm-one hyperplane contains the faithful action of the explicit
Heisenberg subgroup of order 27. The norm-zero hyperplane has a nontrivial
cubic and a derived cyclic-normalizer element moving the hyperplane.
Together these give the model alternatives for the source component argument.

The internal imports deliberately reuse the private Heisenberg coordinates,
whose group law is checked in the owning ATLAS companion. Only intrinsic
subgroups of the original model occur in the public statements.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. Root coordinates
retain the licensed ATLAS attribution; see LICENSES/ATLAS.txt.
-/

public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => commutator (Model F)
local notation "P" => BinaryThreeRank.embedding.range

private theorem heisenberg_parameters_cube :
    ∀ p : BinaryThreeRank.Parameters, p ^ 3 = 1 := by
  decide +kernel

private theorem heisenberg_cube (y : Model F) (hy : y ∈ P) : y ^ 3 = 1 := by
  obtain ⟨p, rfl⟩ := hy
  rw [← map_pow, heisenberg_parameters_cube, map_one]

private theorem heisenberg_stabilizes_seed :
    P ≤ MulAction.stabilizer (Model F) (seed 1) := by
  have hx : BinaryThreeRank.x ∈ MulAction.stabilizer (Model F) (seed 1) := by
    change act BinaryThreeRank.x (seed 1) = seed 1
    decide +kernel
  have hy : BinaryThreeRank.y ∈ MulAction.stabilizer (Model F) (seed 1) := by
    change act BinaryThreeRank.y (seed 1) = seed 1
    decide +kernel
  have hz : BinaryThreeRank.z ∈ MulAction.stabilizer (Model F) (seed 1) :=
    (MulAction.stabilizer (Model F) (seed 1)).mul_mem
      ((MulAction.stabilizer (Model F) (seed 1)).mul_mem
        ((MulAction.stabilizer (Model F) (seed 1)).mul_mem hx hy)
        ((MulAction.stabilizer (Model F) (seed 1)).inv_mem hx))
      ((MulAction.stabilizer (Model F) (seed 1)).inv_mem hy)
  rintro y ⟨p, rfl⟩
  exact (MulAction.stabilizer (Model F) (seed 1)).mul_mem
    ((MulAction.stabilizer (Model F) (seed 1)).mul_mem
      ((MulAction.stabilizer (Model F) (seed 1)).pow_mem hx p.i.val)
      ((MulAction.stabilizer (Model F) (seed 1)).pow_mem hy p.j.val))
    ((MulAction.stabilizer (Model F) (seed 1)).pow_mem hz p.k.val)

/-- On the orbit of 28, an actual derived extraspecial subgroup of order 27
and exponent three acts faithfully on the literal hyperplane. -/
theorem norm_one_extraspecial_actor (a : Parameters) (ha : normClass a = 1) :
    ∃ Y : Subgroup (Model F), Y ≤ D ∧ IsExtraspecial 3 Y ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧
      Y ≤ subspaceStabilizer (traceZeroAction F) (hyperplane a) ∧
      ∀ y ∈ Y, (∀ v ∈ hyperplane a, traceZeroAction F y v = v) → y = 1 := by
  obtain ⟨g, hg⟩ := exists_derived_seed a
  have hg1 : act g.val (seed 1) = a := by simpa only [ha] using hg
  let Y := (BinaryThreeRank.embedding.range).map (MulAut.conj g.val).toMonoidHom
  have hPD : P ≤ D := BinaryThreeRank.image_le_commutator
  have hYP : P ≃* Y := (MulAut.conj g.val).subgroupMap P
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨p, hp, rfl⟩
    exact (commutator (Model F)).mul_mem ((commutator (Model F)).mul_mem g.property (hPD hp)) ((commutator (Model F)).inv_mem g.property)
  · exact IsExtraspecial.of_mulEquiv hYP
      (IsExtraspecial.of_noncommutative_card_prime_cube
        (p := 3) (show Nat.card P = 3 ^ 3 from BinaryThreeRank.card_image)
        BinaryThreeRank.image_noncommutative)
  · exact (Nat.card_congr hYP.toEquiv).symm.trans BinaryThreeRank.card_image
  · rintro y ⟨p, hp, rfl⟩
    rw [← map_pow, heisenberg_cube p hp, map_one]
  · rintro y ⟨p, hp, rfl⟩
    apply (subspace_map_eq_iff (traceZeroAction F) (hyperplane a) _).mp
    rw [map_hyperplane]
    apply congrArg hyperplane
    change act (g.val * p * g.val⁻¹) a = a
    have hgn : act g.val⁻¹ a = seed 1 := by
      conv_lhs => rw [← hg1]
      rw [← act_mul, inv_mul_cancel, act_one]
    rw [act_mul, act_mul, hgn]
    change act g.val (p • seed 1) = a
    rw [heisenberg_stabilizes_seed hp]
    exact hg1
  · intro y _ hfix
    exact pointwise_large_subspace_trivial (hyperplane a)
      (by rw [finrank_hyperplane]; omega) (identity_not_mem a) y hfix

/-- The exact model alternatives used for the ordinary-component elimination.
The cubic mover belongs to the derived group; no square condition is required. -/
theorem cover_hyperplane_component_actors (U : Submodule F E)
    (hdim : Module.finrank F U = 6) (hi : identity F ∉ U) :
    (∃ Y : Subgroup (Model F), Y ≤ D ∧ IsExtraspecial 3 Y ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ≤ subspaceStabilizer (traceZeroAction F) U ∧
      ∀ y ∈ Y, (∀ v ∈ U, traceZeroAction F y v = v) → y = 1) ∨
    (∃ x l : D, orderOf x = 3 ∧ U.map (traceZeroAction F x.val) = U ∧
      (∃ v ∈ U, traceZeroAction F x.val v ≠ v) ∧ l * x * l⁻¹ = x⁻¹ ∧
      l ∈ normalizer (zpowers x : Set D) ∧
      U.map (traceZeroAction F l.val) ≠ U) := by
  obtain ⟨a, rfl⟩ := exists_hyperplane U hdim hi
  by_cases ha : normClass a = 0
  · exact Or.inr (norm_zero_cubic_mover a ha)
  · exact Or.inl (norm_one_extraspecial_actor a
      ((by decide +kernel : ∀ q : F, q ≠ 0 → q = 1) _ ha))

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
