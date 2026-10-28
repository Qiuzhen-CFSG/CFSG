module

public import Theory.Representation.G2Natural
public import Theory.Representation.RepEquiv

/-!
# Coordinates on the characteristic-two natural G₂ module

Deleting the two scalar coordinates identifies the trace-zero octonions modulo
identity with six coordinates. The inverse inserts zeros in both scalar slots.
This is an intertwining equivalence for the actual octonion automorphism group;
the formulas below compute its six positive root actions and two Weyl maps.

Source: GLS3, Example 2.8.10(g). The octonion coordinate conventions and root
maps are those of the attributed ATLAS ports imported by `G2Natural`.
-/

@[expose] public section

namespace Atlas.G2.Restricted.NaturalCoordinates

open Atlas.SplitOctonion

variable (F : Type*) [Field F] [CharP F 2]

/-- Six nonscalar split-octonion coordinates, in order `0,1,2,5,6,7`. -/
abbrev Space := Fin 6 → F

/-- Insert zero scalar coordinates to choose a trace-zero representative. -/
def representative : Space F →ₗ[F] Natural.TraceZero F where
  toFun v := ⟨![v 0, v 1, v 2, 0, 0, v 3, v 4, v 5], by
    simp [Natural.mem_traceZero, trace]⟩
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

/-- Read the six nonscalar coordinates of a trace-zero element. -/
def projection : Natural.TraceZero F →ₗ[F] Space F where
  toFun x := ![x.val 0, x.val 1, x.val 2, x.val 5, x.val 6, x.val 7]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' a x := by ext i; fin_cases i <;> rfl

/-- Reading coordinates kills the scalar identity line. -/
theorem scalarLine_le_ker : Natural.scalarLine F ≤ (projection F).ker := by
  rw [Natural.scalarLine, Submodule.span_singleton_le_iff_mem]
  ext i
  fin_cases i <;> simp [projection, Natural.identity, unit]

/-- Coordinates of the quotient, independent of the representative. -/
def coordinates : Natural.Space F →ₗ[F] Space F :=
  (Natural.scalarLine F).liftQ (projection F) (scalarLine_le_ker F)

/-- A coordinate vector as a class in the actual natural module. -/
def quotientClass : Space F →ₗ[F] Natural.Space F :=
  (Natural.mk F).comp (representative F)

@[simp] theorem coordinates_mk (x : Natural.TraceZero F) :
    coordinates F (Natural.mk F x) = projection F x := rfl

@[simp] theorem coordinates_quotientClass (v : Space F) :
    coordinates F (quotientClass F v) = v := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem quotientClass_coordinates (x : Natural.Space F) :
    quotientClass F (coordinates F x) = x := by
  obtain ⟨y, rfl⟩ := Natural.mk_surjective F x
  apply (Natural.mk_eq_mk_iff F _ _).2
  have hy : y.val 3 + y.val 4 = 0 := y.property
  have heq : y.val 4 = y.val 3 := by
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right hy)
  refine ⟨y.val 3, ?_⟩
  ext i
  fin_cases i <;> simp [representative, projection, unit, heq, CharTwo.neg_eq]

/-- The concrete linear identification, with a specified inverse. -/
def equiv : Natural.Space F ≃ₗ[F] Space F :=
  LinearEquiv.ofLinearMap (coordinates F) (quotientClass F)
    (LinearMap.ext (coordinates_quotientClass F))
    (LinearMap.ext (quotientClass_coordinates F))

@[simp] theorem equiv_apply (x : Natural.Space F) : equiv F x = coordinates F x := rfl

@[simp] theorem equiv_symm_apply (v : Space F) : (equiv F).symm v = quotientClass F v := rfl

/-- Transport of the actual natural representation into these coordinates. -/
def action : Representation F (Model F) (Space F) :=
  (LinearEquiv.conjAlgEquiv F (equiv F)).toMonoidHom.comp (Natural.action F)

/-- Coordinates intertwine the two actions. -/
def repEquiv : Representation.RepEquiv (Natural.action F) (action F) where
  toLinearEquiv := equiv F
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change equiv F (Natural.action F g x) =
      equiv F (Natural.action F g ((equiv F).symm (equiv F x)))
    rw [LinearEquiv.symm_apply_apply]

/-- Compute the coordinate action by lifting to the actual octonions. -/
theorem action_apply (g : Model F) (v : Space F) :
    action F g v = projection F (Natural.traceZeroAction F g (representative F v)) := rfl


@[simp] theorem action_rootA (a : F) (v : Space F) :
    action F (rootA a) v = ![v 0 + a * v 4, v 1 + a * v 5, v 2, v 3, v 4, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootA, Explicit.rootAEquiv, Explicit.rootALinear, Explicit.rootAApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_rootB (a : F) (v : Space F) :
    action F (rootB a) v = ![v 0 + a * v 3, v 1, v 2 + a * v 5, v 3, v 4, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootB, Explicit.rootBEquiv, Explicit.rootBLinear, Explicit.rootBApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_rootC (a : F) (v : Space F) :
    action F (rootC a) v = ![v 0 + a^2 * v 5, v 1 + a * v 3, v 2 + a * v 4, v 3, v 4, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootC, Explicit.rootCEquiv, Explicit.rootCLinear, Explicit.rootCApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_rootD (a : F) (v : Space F) :
    action F (rootD a) v = ![v 0 + a * v 2, v 1 + a^2 * v 4, v 2, v 3 + a * v 5, v 4, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootD, Explicit.rootDEquiv, Explicit.rootDLinear, Explicit.rootDApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_rootE (a : F) (v : Space F) :
    action F (rootE a) v = ![v 0, v 1 + a * v 2, v 2, v 3 + a * v 4, v 4, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootE, Explicit.rootEEquiv, Explicit.rootELinear, Explicit.rootEApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_rootF (a : F) (v : Space F) :
    action F (rootF a) v = ![v 0 + a * v 1, v 1, v 2 + a^2 * v 3, v 3, v 4 + a * v 5, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      rootF, Explicit.rootFEquiv, Explicit.rootFLinear, Explicit.rootFApply,
      sub_eq_add_neg, CharTwo.neg_eq]

@[simp] theorem action_weylR (v : Space F) :
    action F weylR v = ![v 0, v 2, v 1, v 4, v 3, v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      weylR, weylREquiv, weylRLinear, weylRApply, CharTwo.neg_eq]

@[simp] theorem action_weylS (v : Space F) :
    action F weylS v = ![v 1, v 0, v 3, v 2, v 5, v 4] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      weylS, weylSEquiv, weylSLinear, weylSApply, CharTwo.neg_eq]

end Atlas.G2.Restricted.NaturalCoordinates
