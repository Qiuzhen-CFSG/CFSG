module

public import Theory.Representation.G2OrthogonalCover.HyperplaneMaximalityOne
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction

/-!
# Maximal literal hyperplane stabilizers for intermediate binary G₂ actors

An actor subgroup containing the actual derived group inherits both primitive
orbits. Equivariance of the canonical hyperplane coordinates identifies its
point stabilizers with the literal subspace stabilizers in the trace-zero
seven-space. Their indices are 36 or 28, and hence never two.

The intermediate actor is retained: the application to LT needs no claim
that its image equals full G₂(2).

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. This supplies the
maximal-stabilizer premise used for the original chosen cover hyperplanes.
-/

public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes
open Representation.BinaryOffender
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => commutator (Model F)

private theorem derived_primitive (q : F) : MulAction.IsPreprimitive D (Fibre q) := by
  have hc : q = 0 ∨ q = 1 := (by decide +kernel : ∀ a : F, a = 0 ∨ a = 1) q
  rcases hc with rfl | rfl <;> infer_instance

private theorem fibre_nontrivial (q : F) : Nontrivial (Fibre q) := by
  have hc : q = 0 ∨ q = 1 := (by decide +kernel : ∀ a : F, a = 0 ∨ a = 1) q
  rcases hc with rfl | rfl <;> infer_instance

/-- Every actual actor containing the derived group retains the primitive orbits. -/
theorem intermediate_primitive (K : Subgroup (Model F)) (hK : D ≤ K) (q : F) :
    MulAction.IsPreprimitive K (Fibre q) := by
  let := derived_primitive q
  let f : Fibre q →ₑ[Subgroup.inclusion hK] Fibre q := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

instance full_primitive (q : F) : MulAction.IsPreprimitive (Model F) (Fibre q) := by
  let := derived_primitive q
  let f : Fibre q →ₑ[(commutator (Model F)).subtype] Fibre q := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- The abstract orbit stabilizer is the literal seven-space stabilizer. -/
theorem stabilizer_eq_subspaceStabilizer (K : Subgroup (Model F)) (q : F) (a : Fibre q) :
    MulAction.stabilizer K a =
      subspaceStabilizer ((traceZeroAction F).comp K.subtype) (hyperplane a.val) := by
  ext g
  rw [← subspace_map_eq_iff]
  change g • a = a ↔
    (hyperplane a.val).map (traceZeroAction F g.val) = hyperplane a.val
  rw [map_hyperplane]
  exact ⟨fun he => congrArg hyperplane (congrArg Subtype.val he),
    fun he => Subtype.ext (hyperplane_injective he)⟩

theorem isCoatom_intermediate_stabilizer (K : Subgroup (Model F)) (hK : D ≤ K)
    (q : F) (a : Fibre q) : IsCoatom (MulAction.stabilizer K a) := by
  let := intermediate_primitive K hK q
  let := fibre_nontrivial q
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive K a

theorem index_intermediate_stabilizer (K : Subgroup (Model F)) (hK : D ≤ K)
    (q : F) (a : Fibre q) :
    (MulAction.stabilizer K a).index = if q = 0 then 36 else 28 := by
  let := intermediate_primitive K hK q
  rw [MulAction.index_stabilizer_of_transitive]
  by_cases hq : q = 0
  · rw [hq, if_pos rfl]
    exact card_fibre_zero
  · have hq1 : q = 1 := (by decide +kernel : ∀ a : F, a ≠ 0 → a = 1) q hq
    rw [hq1, if_neg one_ne_zero]
    exact card_fibre_one

/-- The literal stabilizer of every off-scalar cover hyperplane is maximal,
with index 36 or 28, in any actor containing the actual derived group. -/
theorem cover_hyperplane_stabilizer (K : Subgroup (Model F)) (hK : D ≤ K)
    (U : Submodule F E) (hdim : Module.finrank F U = 6)
    (hi : identity F ∉ U) :
    IsCoatom (subspaceStabilizer ((traceZeroAction F).comp K.subtype) U) ∧
      ((subspaceStabilizer ((traceZeroAction F).comp K.subtype) U).index = 36 ∨
       (subspaceStabilizer ((traceZeroAction F).comp K.subtype) U).index = 28) := by
  obtain ⟨a, rfl⟩ := exists_hyperplane U hdim hi
  let b : Fibre (normClass a) := ⟨a, rfl⟩
  rw [← stabilizer_eq_subspaceStabilizer K (normClass a) b]
  refine ⟨isCoatom_intermediate_stabilizer K hK _ b, ?_⟩
  rw [index_intermediate_stabilizer K hK]
  split <;> simp

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
