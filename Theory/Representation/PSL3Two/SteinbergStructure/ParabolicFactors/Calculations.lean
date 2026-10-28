module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates

/-!
# Coordinates of a chief series for the point parabolic

The trace-zero matrices have an invariant flag of dimensions 0, 2, 3, 5, 6, 8.
The first two coordinates are the upper-right row; the next layer adds the
scalar lower-right block, followed by its two off-diagonal entries, the remaining
diagonal coordinate, and the lower-left column. The certificates below check
stability on basis vectors and compute the five section actions. A local element
of order three generates each two-dimensional section from any nonzero vector.

These are kernel-checked calculations for the actual matrix action in
Aschbacher–Smith H.6.3(3), printed pp.387–388 (1 March 2004 manuscript).
-/

@[expose] public section
open Matrix Representation
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue Matrix.PSL3Two
namespace BinaryLinearThree.SteinbergStructure.ParabolicFactors.Calculations
def allowed : Fin 6 → Fin 8 → Bool :=
  ![![false,false,false,false,false,false,false,false],
    ![true,true,false,false,false,false,false,false],
    ![true,true,false,false,false,false,false,true],
    ![true,true,false,true,false,true,false,true],
    ![true,true,false,true,false,true,true,true],
    ![true,true,true,true,true,true,true,true]]
def inLayer (i : Fin 6) (v : Eight) : Prop := ∀ j, allowed i j = false → v j = 0
instance (i : Fin 6) (v : Eight) : Decidable (inLayer i v) := inferInstanceAs (Decidable (∀ _j, _))
def coordinateLayer (i : Fin 6) : Submodule (ZMod 2) Eight where
  carrier := {v | inLayer i v}
  zero_mem' := by intro j hj; rfl
  add_mem' := by intro v w hv hw j hj; change v j + w j = 0; rw [hv j hj, hw j hj, zero_add]
  smul_mem' := by intro c v hv j hj; change c * v j = 0; rw [hv j hj, mul_zero]
def action (g : Group) (v : Eight) : Eight :=
  readMatrix (g.val * matrixOf v * g⁻¹.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem invariant_certificate : ∀ (i : Fin 6) (g : Group),
    g.val 1 0 = 0 → g.val 2 0 = 0 → ∀ j : Fin 8,
    allowed i j = true → inLayer i (action g (Pi.single j 1)) := by decide +kernel

def cubic : Group := ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩
theorem cubic_mem : cubic ∈ pointParabolicSL := by decide
def sectionCoord (i : Fin 5) (v : Eight) : ZMod 2 × ZMod 2 :=
  (![(v 0,v 1),(v 7,0),(v 3,v 5),(v 6,0),(v 2,v 4)] : Fin 5 → ZMod 2 × ZMod 2) i
def smallAction (i : Fin 5) (v : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  if i = 0 then (v.1 + v.2,v.1) else if i = 2 ∨ i = 4 then (v.2,v.1+v.2) else v
def valid (i : Fin 5) (v : ZMod 2 × ZMod 2) : Prop :=
  i = 0 ∨ i = 2 ∨ i = 4 ∨ v.2 = 0
instance (i : Fin 5) (v : ZMod 2 × ZMod 2) : Decidable (valid i v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
def sectionMap (i : Fin 5) : Eight →ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun := sectionCoord i
  map_add' v w := by fin_cases i <;> simp [sectionCoord]
  map_smul' c v := by fin_cases i <;> simp [sectionCoord]
set_option maxRecDepth 100000 in
theorem layer_kernel : ∀ (i : Fin 5) (v : Eight), inLayer i.succ v →
    (inLayer i.castSucc v ↔ sectionCoord i v = 0) := by decide +kernel
set_option maxRecDepth 100000 in
theorem section_action : ∀ (i : Fin 5) (v : Eight), inLayer i.succ v →
    sectionCoord i (action cubic v) = smallAction i (sectionCoord i v) := by decide +kernel
theorem section_valid : ∀ (i : Fin 5) (v : Eight), valid i (sectionCoord i v) := by decide +kernel
set_option synthInstance.maxSize 256 in
theorem simple_certificate : ∀ (i : Fin 5) (x y : ZMod 2 × ZMod 2),
    valid i x → x ≠ 0 → valid i y →
    ∃ a b : ZMod 2, y = a • x + b • smallAction i x := by decide +kernel
theorem layer_inclusion : ∀ (i : Fin 5) (v : Eight),
    inLayer i.castSucc v → inLayer i.succ v := by decide +kernel
theorem layer_strict : ∀ i : Fin 5, ∃ v : Eight,
    inLayer i.succ v ∧ ¬ inLayer i.castSucc v := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem central_certificate : ∀ (i : Fin 5), i = 1 ∨ i = 3 → ∀ (g : Group),
    g.val 1 0 = 0 → g.val 2 0 = 0 → ∀ j : Fin 8,
    allowed i.succ j = true → inLayer i.castSucc (action g (Pi.single j 1) - Pi.single j 1) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem noncentral_certificate : ∀ (i : Fin 5), ¬ (i = 1 ∨ i = 3) → ∃ v : Eight,
    inLayer i.succ v ∧ ¬ inLayer i.castSucc (action cubic v - v) := by decide +kernel


end BinaryLinearThree.SteinbergStructure.ParabolicFactors.Calculations
