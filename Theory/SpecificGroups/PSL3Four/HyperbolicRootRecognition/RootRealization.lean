module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.BinaryModel
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel

/-!
# The two hyperbolic word groups are the literal UT₃(F₄)

The common generators are a=(1,0,0), b=(0,1,0), z=(0,0,1),
u=(0,0,ω). For the aligned cross matrix use c=(ω+1,0,0) and
d=(0,ω+1,0); interchange c,d for the crossed matrix. Ordered evaluation
adds the explicit central quadratic correction. The identity ω²=ω+1
checks the multiplication, and the four binary root coordinates are
independent. Thus the map is an actual group equivalence.

The two root axes are retained in their original word coordinates for
transport of the source reflection actions. Source: Aschbacher,
*Sporadic Groups* (1994), 45.3, printed pp.242–243.
-/

public section

open Matrix.PSL3Four Matrix.PSL3Four.SylowModel
namespace Theory.GroupTheory.HyperbolicRecognition
noncomputable section

private def bitCast : Bit →+* F := ZMod.castHom (dvd_refl 2) F

private def fieldValue (p : Central) : F := bitCast p.1 + omega * bitCast p.2

private def fieldMul (p q : Central) : Central :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

private theorem fieldValue_add (p q : Central) :
    fieldValue (p+q) = fieldValue p + fieldValue q := by
  simp only [fieldValue, Prod.fst_add, Prod.snd_add, map_add]
  ring

private theorem fieldValue_mul (p q : Central) :
    fieldValue (fieldMul p q) = fieldValue p * fieldValue q := by
  have hw : omega ^ 2 = omega + 1 := by
    rw [← fieldFrobenius_apply, omega_frobenius]
  dsimp [fieldValue, fieldMul]
  simp only [map_add, map_mul]
  calc
    _ = bitCast p.1 * bitCast q.1 + omega * (bitCast p.1 * bitCast q.2 +
      bitCast p.2 * bitCast q.1) + (omega + 1) * (bitCast p.2 * bitCast q.2) := by ring
    _ = _ := by rw [← hw]; ring

private theorem fieldValue_injective : Function.Injective fieldValue := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have bit_cases : ∀ x : Bit, x = 0 ∨ x = 1 := by decide +kernel
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl <;>
    simp_all [fieldValue, omega_ne_zero, omega_ne_one,
      Ne.symm omega_ne_zero, Ne.symm omega_ne_one, CharTwo.add_eq_zero]
  exact omega_ne_one (CharTwo.add_eq_zero.mp h.symm).symm

private def scale (t : Bit) (p : Central) : Central := (t * p.1, t * p.2)

private def rootX (c d : Central × Central) (v : Vector) : Central :=
  scale v.1.1 cz + scale v.2.1 c.1 + scale v.2.2 d.1

private def rootY (c d : Central × Central) (v : Vector) : Central :=
  scale v.1.2 cz + scale v.2.1 c.2 + scale v.2.2 d.2

private def correction (c d : Central × Central) (v : Vector) : Central :=
  scale (v.1.1 * v.1.2) cz +
  scale (v.1.1 * v.2.1) (fieldMul cz c.2) +
  scale (v.1.1 * v.2.2) (fieldMul cz d.2) +
  scale (v.2.1 * v.2.2) (fieldMul c.1 d.2)

private def rootC : Central × Central := (czu, 0)
private def rootD : Central × Central := (0, czu)

private theorem rootX_add (c d : Central × Central) (v w : Vector) :
    rootX c d (v + w) = rootX c d v + rootX c d w := by
  ext <;> dsimp [rootX,scale] <;> ring

private theorem rootY_add (c d : Central × Central) (v w : Vector) :
    rootY c d (v + w) = rootY c d v + rootY c d w := by
  ext <;> dsimp [rootY,scale] <;> ring

/-- The two multiplication laws selected by the source reflections. -/
@[expose] def modelMatrix : Fin 2 → Cross
  | 0 => alignedMatrix
  | 1 => crossedMatrix

private def modelParameters : Fin 2 → (Central × Central) × (Central × Central)
  | 0 => (rootC, rootD)
  | 1 => (rootD, rootC)

private theorem model_collection (i : Fin 2) (v w : Vector) :
    cocycle (modelMatrix i) v w +
      correction (modelParameters i).1 (modelParameters i).2 (v + w) =
    correction (modelParameters i).1 (modelParameters i).2 v +
      correction (modelParameters i).1 (modelParameters i).2 w +
      fieldMul (rootX (modelParameters i).1 (modelParameters i).2 v)
        (rootY (modelParameters i).1 (modelParameters i).2 w) := by
  fin_cases i <;> ext <;>
    dsimp [modelMatrix, modelParameters, cocycle, correction, rootX, rootY,
      rootC, rootD, alignedMatrix, crossedMatrix, scale, fieldMul, cz, cu, czu] <;>
    ring_nf <;>
    simp [show (2 : Bit) = 0 by decide, show (3 : Bit) = 1 by decide, show (4 : Bit) = 0 by decide]

private theorem model_vector_injective : ∀ (i : Fin 2) (v w : Vector),
    rootX (modelParameters i).1 (modelParameters i).2 v =
      rootX (modelParameters i).1 (modelParameters i).2 w →
    rootY (modelParameters i).1 (modelParameters i).2 v =
      rootY (modelParameters i).1 (modelParameters i).2 w → v = w := by
  decide +kernel

private def modelMap (i : Fin 2) (p : Word (modelMatrix i)) :
    RootNormalizerModel.Root :=
  ⟨fieldValue (rootX (modelParameters i).1 (modelParameters i).2 p.vector),
    fieldValue (rootY (modelParameters i).1 (modelParameters i).2 p.vector),
    fieldValue (p.central +
      correction (modelParameters i).1 (modelParameters i).2 p.vector)⟩

private def modelHom (i : Fin 2) : Word (modelMatrix i) →* RootNormalizerModel.Root where
  toFun := modelMap i
  map_one' := by
    apply U.ext <;>
      simp [modelMap, rootX, rootY, correction, scale, fieldValue]
  map_mul' p q := by
    apply U.ext
    · change fieldValue (rootX _ _ (p.vector + q.vector)) = _
      rw [rootX_add, fieldValue_add]
      rfl
    · change fieldValue (rootY _ _ (p.vector + q.vector)) = _
      rw [rootY_add, fieldValue_add]
      rfl
    · change fieldValue ((p.central + q.central + cocycle (modelMatrix i) p.vector q.vector) +
        correction (modelParameters i).1 (modelParameters i).2 (p.vector + q.vector)) = _
      rw [add_assoc (p.central + q.central), model_collection]
      simp only [fieldValue_add, fieldValue_mul, mul_c, modelMap]
      abel

private theorem modelHom_injective (i : Fin 2) : Function.Injective (modelHom i) := by
  intro p q h
  have hx := fieldValue_injective (congrArg U.x h)
  have hy := fieldValue_injective (congrArg U.y h)
  have hv := model_vector_injective i p.vector q.vector hx hy
  apply Word.ext hv
  have hc := fieldValue_injective (congrArg U.c h)
  change p.central + correction _ _ p.vector = q.central + correction _ _ q.vector at hc
  rw [hv] at hc
  exact add_right_cancel hc

/-- The explicit ordered-word realization in the literal root group. -/
def modelEquiv (i : Fin 2) : Word (modelMatrix i) ≃* RootNormalizerModel.Root :=
  MulEquiv.ofBijective (modelHom i)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨modelHom_injective i, (card_Word _).trans card_U.symm⟩)

/-- Either surviving multiplication law is the actual root group. -/
theorem rootEquiv_of_twoCases (M : Cross) (hM : TwoCases M) :
    Nonempty (Word M ≃* RootNormalizerModel.Root) := by
  rcases hM with rfl | rfl
  · exact ⟨modelEquiv 0⟩
  · exact ⟨modelEquiv 1⟩

/-- The binary equations for the first root plane, where y vanishes. -/
@[expose] def modelFirstAxis (i : Fin 2) (v : Vector) : Prop :=
  if i = 0 then v.1.2 = 0 ∧ v.2.2 = 0 else v.1.2 = 0 ∧ v.2.1 = 0

/-- The binary equations for the second root plane, where x vanishes. -/
@[expose] def modelSecondAxis (i : Fin 2) (v : Vector) : Prop :=
  if i = 0 then v.1.1 = 0 ∧ v.2.1 = 0 else v.1.1 = 0 ∧ v.2.2 = 0

instance (i : Fin 2) (v : Vector) : Decidable (modelFirstAxis i v) := by
  unfold modelFirstAxis
  infer_instance
instance (i : Fin 2) (v : Vector) : Decidable (modelSecondAxis i v) := by
  unfold modelSecondAxis
  infer_instance

private theorem rootY_zero_iff (i : Fin 2) (v : Vector) :
    rootY (modelParameters i).1 (modelParameters i).2 v = 0 ↔ modelFirstAxis i v := by
  have h : ∀ (i : Fin 2) (v : Vector),
      rootY (modelParameters i).1 (modelParameters i).2 v = 0 ↔ modelFirstAxis i v := by
    decide +kernel
  exact h i v

private theorem rootX_zero_iff (i : Fin 2) (v : Vector) :
    rootX (modelParameters i).1 (modelParameters i).2 v = 0 ↔ modelSecondAxis i v := by
  have h : ∀ (i : Fin 2) (v : Vector),
      rootX (modelParameters i).1 (modelParameters i).2 v = 0 ↔ modelSecondAxis i v := by
    decide +kernel
  exact h i v

/-- The literal y-coordinate detects the first binary axis. -/
theorem modelEquiv_y_eq_zero (i : Fin 2) (w : Word (modelMatrix i)) :
    (modelEquiv i w).y = 0 ↔ modelFirstAxis i w.vector := by
  change fieldValue (rootY (modelParameters i).1 (modelParameters i).2 w.vector) = 0 ↔ _
  rw [← show fieldValue 0 = 0 by simp [fieldValue], fieldValue_injective.eq_iff,
    rootY_zero_iff]

/-- The literal x-coordinate detects the second binary axis. -/
theorem modelEquiv_x_eq_zero (i : Fin 2) (w : Word (modelMatrix i)) :
    (modelEquiv i w).x = 0 ↔ modelSecondAxis i w.vector := by
  change fieldValue (rootX (modelParameters i).1 (modelParameters i).2 w.vector) = 0 ↔ _
  rw [← show fieldValue 0 = 0 by simp [fieldValue], fieldValue_injective.eq_iff,
    rootX_zero_iff]

end
end Theory.GroupTheory.HyperbolicRecognition
