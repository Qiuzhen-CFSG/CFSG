module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Transport

/-!
# The two factors in the local A₅ action

The first SL₂ acts on coordinates (0,5); the second acts on both (1,3)
and (2,4). The resulting faithful representation keeps the literal octonion
coordinate order. The pair of flips is `graph`, and the pair of upper
unitriangular involutions is `rootC 1`.

These are the linear factors used on p.284 of Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5. `LocalA5.Data` uses this action to state the remaining
Leech construction independently of the diagonal identification.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
variable {K : Type*} [Field K] [CharP K 2]

/-- The shared reflection of the two factors. -/
def flip : SL(2,K) := ⟨!![0,1;1,0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

/-- The upper unitriangular involution. -/
def shear : SL(2,K) := ⟨!![1,1;0,1], by simp [Matrix.det_fin_two]⟩

/-- The diagonal torus of either factor. -/
def torus (t : Kˣ) : SL(2,K) :=
  ⟨!![(t : K),0;0,(t⁻¹ : Kˣ)], by simp [Matrix.det_fin_two]⟩

def pairAction (p : SL(2,K) × SL(2,K)) (v : Fin 6 → K) : Fin 6 → K :=
  ![p.1.val 0 0 * v 0 + p.1.val 0 1 * v 5,
    p.2.val 0 0 * v 1 + p.2.val 0 1 * v 3,
    p.2.val 0 0 * v 2 + p.2.val 0 1 * v 4,
    p.2.val 1 0 * v 1 + p.2.val 1 1 * v 3,
    p.2.val 1 0 * v 2 + p.2.val 1 1 * v 4,
    p.1.val 1 0 * v 0 + p.1.val 1 1 * v 5]

omit [CharP K 2] in
theorem pairAction_mul (p q : SL(2,K) × SL(2,K)) (v : Fin 6 → K) :
    pairAction (p * q) v = pairAction p (pairAction q v) := by
  funext i
  fin_cases i <;>
    simp [pairAction, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

omit [CharP K 2] in
theorem pairAction_one (v : Fin 6 → K) : pairAction 1 v = v := by
  funext i
  fin_cases i <;> simp [pairAction]

def pairLinear (p : SL(2,K) × SL(2,K)) : (Fin 6 → K) →ₗ[K] (Fin 6 → K) where
  toFun := pairAction p
  map_add' v w := by
    funext i
    fin_cases i <;> simp [pairAction] <;> ring
  map_smul' a v := by
    funext i
    fin_cases i <;> simp [pairAction] <;> ring

def pairRepresentation : (SL(2,K) × SL(2,K)) →* ((Fin 6 → K) ≃ₗ[K] (Fin 6 → K)) where
  toFun p :=
    { toLinearMap := pairLinear p
      invFun := pairAction p⁻¹
      left_inv v := by
        change pairAction p⁻¹ (pairAction p v) = v
        rw [← pairAction_mul, inv_mul_cancel, pairAction_one]
      right_inv v := by
        change pairAction p (pairAction p⁻¹ v) = v
        rw [← pairAction_mul, mul_inv_cancel, pairAction_one] }
  map_one' := by
    apply LinearEquiv.ext
    exact pairAction_one
  map_mul' p q := by
    apply LinearEquiv.ext
    exact pairAction_mul p q

omit [CharP K 2] in
theorem pairRepresentation_injective : Function.Injective (pairRepresentation (K := K)) := by
  intro p q h
  have he (v : Fin 6 → K) (i : Fin 6) : pairAction p v i = pairAction q v i :=
    congrFun (LinearEquiv.congr_fun h v) i
  apply Prod.ext
  · apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [pairAction] using he (Pi.single 0 1) 0
    · simpa [pairAction] using he (Pi.single 5 1) 0
    · simpa [pairAction] using he (Pi.single 0 1) 5
    · simpa [pairAction] using he (Pi.single 5 1) 5
  · apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [pairAction] using he (Pi.single 1 1) 1
    · simpa [pairAction] using he (Pi.single 3 1) 1
    · simpa [pairAction] using he (Pi.single 1 1) 3
    · simpa [pairAction] using he (Pi.single 3 1) 3

theorem graph_action (v : Fin 6 → K) :
    pairRepresentation (flip, flip) v =
      Atlas.G2.ConwayRootFour.OctonionLocals.action
        Atlas.G2.ConwayRootFour.OctonionLocals.graph v := by
  rw [Atlas.G2.ConwayRootFour.OctonionLocals.action_graph]
  change pairAction (flip, flip) v = _
  simp [pairAction, flip]

theorem shear_action (v : Fin 6 → K) :
    pairRepresentation (shear, shear) v =
      Atlas.G2.ConwayRootFour.OctonionLocals.action (Atlas.G2.rootC 1) v := by
  rw [Atlas.G2.ConwayRootFour.OctonionLocals.action_rootC]
  change pairAction (shear, shear) v = _
  simp [pairAction, shear]


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
