module

public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates

/-!
# The actual binary Fano flag action

Lines are the tagged covectors in the Fano plane. Their action is inverse
transpose, identified with the actual natural dual by the dot product. Flags
are incident point-line pairs. This file supplies their permutation module
and the line augmentation core, independently of any irreducible catalogue.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5–H.6,
printed pp.385–387.
-/

@[expose] public section
open Matrix Representation
namespace BinaryLinearThree.FanoDecomposition

abbrev Line := Matrix.PSL3Two.Fano.Line
abbrev Dual := Module.Dual (ZMod 2) Vector
abbrev Flag := {pl : Point × Line // Matrix.PSL3Two.Fano.Incident pl.1 pl.2}
abbrev LineCore := BinaryPermutation.core Line

/-- The functional belonging to a tagged Fano line. -/
def lineFunctional (l : Line) : Dual := dotProductEquiv (ZMod 2) (Fin 3) l.normal.val

/-- Inverse transpose on the seven tagged covectors. -/
def linePerm : Group →* Equiv.Perm Line :=
  (Matrix.PSL3Two.Fano.duality.permCongrHom).toMonoidHom.comp
    (pointPerm.comp AutomorphismAction.graph.toMonoidHom)

@[simp] theorem linePerm_normal (g : Group) (l : Line) :
    (linePerm g l).normal = pointPerm (AutomorphismAction.graph g) l.normal := rfl

/-- The line action is precisely precomposition by the inverse natural action. -/
theorem lineFunctional_action (g : Group) (l : Line) :
    lineFunctional (linePerm g l) = W.dual g (lineFunctional l) := by
  apply LinearMap.ext
  intro v
  change ((g⁻¹.val)ᵀ *ᵥ l.normal.val) ⬝ᵥ v = l.normal.val ⬝ᵥ (g⁻¹.val *ᵥ v)
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

theorem incident_iff (p : Point) (l : Line) :
    Matrix.PSL3Two.Fano.Incident p l ↔ lineFunctional l p.val = 0 := by
  change p.val ⬝ᵥ l.normal.val = 0 ↔ l.normal.val ⬝ᵥ p.val = 0
  rw [dotProduct_comm]

theorem incident_action (g : Group) (p : Point) (l : Line)
    (h : Matrix.PSL3Two.Fano.Incident p l) :
    Matrix.PSL3Two.Fano.Incident (pointPerm g p) (linePerm g l) := by
  rw [incident_iff, lineFunctional_action]
  change lineFunctional l (g⁻¹ • (g • p.val)) = 0
  simpa only [inv_smul_smul] using (incident_iff p l).mp h

/-- The genuine action on the twenty-one incident flags. -/
def flagPerm : Group →* Equiv.Perm Flag where
  toFun g :=
    { toFun f := ⟨(pointPerm g f.val.1, linePerm g f.val.2),
        incident_action g _ _ f.property⟩
      invFun f := ⟨(pointPerm g⁻¹ f.val.1, linePerm g⁻¹ f.val.2),
        incident_action g⁻¹ _ _ f.property⟩
      left_inv f := by apply Subtype.ext; simp
      right_inv f := by apply Subtype.ext; simp }
  map_one' := by ext f : 1; apply Subtype.ext; simp
  map_mul' g h := by ext f : 1; apply Subtype.ext; simp

@[simp] theorem flagPerm_point (g : Group) (f : Flag) :
    (flagPerm g f).val.1 = pointPerm g f.val.1 := rfl
@[simp] theorem flagPerm_line (g : Group) (f : Flag) :
    (flagPerm g f).val.2 = linePerm g f.val.2 := rfl

/-- The permutation representation on the actual twenty-one flags. -/
def flagRepresentation : Representation (ZMod 2) Group (BinaryPermutation.Full Flag) :=
  (BinaryPermutation.representation Flag).comp flagPerm

/-- The augmentation kernel of the seven tagged covectors. -/
def lineCoreRepresentation : Representation (ZMod 2) Group LineCore :=
  (BinaryPermutation.coreRepresentation Line).comp linePerm

theorem card_flags : Fintype.card Flag = 21 := Matrix.PSL3Two.Fano.card_flags

/-- Coordinate duality of the two augmentation kernels, without an assertion
that the natural and contragredient group actions agree. -/
def coreDuality : Core ≃ₗ[ZMod 2] LineCore where
  toFun a := ⟨fun l => a.val l.normal, by
    change ∑ l : Line, a.val l.normal = 0
    rw [← Equiv.sum_comp Matrix.PSL3Two.Fano.duality]
    exact a.property⟩
  invFun a := ⟨fun p => a.val (Matrix.PSL3Two.Fano.duality p), by
    change ∑ p : Point, a.val (Matrix.PSL3Two.Fano.duality p) = 0
    rw [Equiv.sum_comp]
    exact a.property⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl
  map_add' a b := rfl
  map_smul' c a := rfl

@[simp] theorem coreDuality_apply (a : Core) (l : Line) :
    (coreDuality a).val l = a.val l.normal := rfl
@[simp] theorem coreDuality_symm_apply (a : LineCore) (p : Point) :
    (coreDuality.symm a).val p = a.val (Matrix.PSL3Two.Fano.duality p) := rfl

/-- Coordinate duality intertwines the inverse-transpose twist. -/
def coreDualityEquiv : Representation.Equiv
    (U₂.comp AutomorphismAction.graph.toMonoidHom) lineCoreRepresentation where
  toLinearEquiv := coreDuality
  isIntertwining' g := by ext a l; rfl

end BinaryLinearThree.FanoDecomposition
