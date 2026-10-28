module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Mathlib.Algebra.Field.ZMod

/-!
# Local relations for the binary exterior square and cube

For each of the two exterior models of SL₅(2), take the wedge of the initial
coordinate frame. We specify its stabilizer relation and one three-term
Grassmann-line relation. The latter expresses additivity in the last coordinate;
the two matrices involved add, respectively exchange, the next coordinate.

A coordinate determinant proves that the standard vector is nonzero. Direct
matrix calculations followed by multilinearity prove the three-term relation.
The assertions here concern the models themselves: extracting a vector with
these relations in an arbitrary irreducible module and proving the universal
presentation are separate results needed by `Classification.lean`.

The intended application is the module identification for Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

/-- Index the exterior square and cube by the two elements of `Fin 2`. -/
def degree (a : Fin 2) : ℕ := a.val + 2

/-- The first two or three standard coordinate vectors of the natural module. -/
def frame (a : Fin 2) (i : Fin (degree a)) : Fin 5 → ZMod 2 :=
  Pi.single (Fin.castLE (by dsimp [degree]; omega) i) 1

/-- The standard decomposable exterior vector. -/
noncomputable def seed (a : Fin 2) : ExteriorModule (degree a) :=
  exteriorPower.ιMulti (ZMod 2) (degree a) (frame a)

private def projection (a : Fin 2) : (Fin 5 → ZMod 2) →ₗ[ZMod 2]
    (Fin (degree a) → ZMod 2) where
  toFun v i := v (Fin.castLE (by dsimp [degree]; omega) i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A coordinate determinant takes the value one on the standard exterior vector. -/
theorem seed_ne_zero (a : Fin 2) : seed a ≠ 0 := by
  let d := (Matrix.detRowAlternating (R := ZMod 2) (n := Fin (degree a))).compLinearMap
    (projection a)
  let f := exteriorPower.alternatingMapLinearEquiv d
  have hmatrix : (fun i => projection a (frame a i)) = (1 : Matrix (Fin (degree a))
      (Fin (degree a)) (ZMod 2)) := by
    ext i j
    simp [projection, frame, Pi.single_apply, Matrix.one_apply, Fin.ext_iff, eq_comm]
  have hf : f (seed a) = 1 := by
    change exteriorPower.alternatingMapLinearEquiv d
      (exteriorPower.ιMulti (ZMod 2) (degree a) (frame a)) = 1
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change Matrix.det (fun i => projection a (frame a i)) = 1
    rw [hmatrix, Matrix.det_one]
  intro hzero
  rw [hzero, map_zero] at hf
  exact zero_ne_one hf

/-- Add the next coordinate vector to the last vector of the standard frame. -/
def step (a : Fin 2) : Group :=
  Matrix.SpecialLinearGroup.transvection
    (i := ⟨a.val + 2, by omega⟩) (j := ⟨a.val + 1, by omega⟩)
    (by intro h; simp only [Fin.mk.injEq] at h; omega) (1 : ZMod 2)

/-- Exchange the last coordinate in the frame with the next coordinate. -/
def swap (a : Fin 2) : Group :=
  let reverseStep : Group := Matrix.SpecialLinearGroup.transvection
    (i := ⟨a.val + 1, by omega⟩) (j := ⟨a.val + 2, by omega⟩)
    (by intro h; simp only [Fin.mk.injEq] at h; omega) (1 : ZMod 2)
  step a * reverseStep * step a

private theorem frame_step (a : Fin 2) :
    (fun i => Matrix.mulVec (step a).val (frame a i)) =
      Function.update (frame a) (Fin.last (a.val + 1))
        (frame a (Fin.last (a.val + 1)) + Pi.single ⟨a.val + 2, by omega⟩ 1) := by
  revert a
  decide

private theorem frame_swap (a : Fin 2) :
    (fun i => Matrix.mulVec (swap a).val (frame a i)) =
      Function.update (frame a) (Fin.last (a.val + 1))
        (Pi.single ⟨a.val + 2, by omega⟩ 1) := by
  revert a
  decide

set_option backward.isDefEq.respectTransparency false in
/-- The three points of a binary Grassmann line sum to zero in the exterior model. -/
theorem seed_relation (a : Fin 2) :
    seed a + exteriorAction (degree a) (swap a) (seed a) +
      exteriorAction (degree a) (step a) (seed a) = 0 := by
  have hstep : exteriorAction (degree a) (step a) (seed a) =
      seed a + exteriorAction (degree a) (swap a) (seed a) := by
    simp only [seed, exteriorAction_ιMulti, frame_step, frame_swap]
    rw [AlternatingMap.map_update_add, Function.update_eq_self]
  rw [hstep]
  generalize seed a + exteriorAction (degree a) (swap a) (seed a) = x
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [htwo, zero_smul]

/-- A vector fixed by the standard decomposable-vector stabilizer and satisfying
the standard Grassmann-line relation. This is an explicit local condition,
with no irreducibility or representation equivalence built into its definition. -/
def HasExteriorSeed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (a : Fin 2) (v : V) : Prop :=
  (∀ g : Group, exteriorAction (degree a) g (seed a) = seed a → ρ g v = v) ∧
    v + ρ (swap a) v + ρ (step a) v = 0

/-- The actual exterior model satisfies the local relations. -/
theorem seed_satisfies_relations (a : Fin 2) :
    HasExteriorSeed (exteriorAction (degree a)) a (seed a) := by
  exact ⟨fun _ h => h, seed_relation a⟩

/-- Both models selected by the two indices have dimension ten. -/
theorem finrank_model (a : Fin 2) :
    Module.finrank (ZMod 2) (ExteriorModule (degree a)) = 10 := by
  fin_cases a
  · exact finrank_exteriorModule_two
  · exact finrank_exteriorModule_three

end Representation.SL5TenDimensional.Classification
