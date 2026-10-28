module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The characteristic-two Clifford action on four-bit coordinates

Creation and annihilation toggle one bit in a sixteen-dimensional space.
Their linear combination squares to the hyperbolic quadratic form, so the
Clifford universal property gives an algebra homomorphism. The eight even
bit strings are ordered to carry the D4 arm cycle `0 → 2 → 3 → 0`.
The embedding is injective; preservation by Spin is proved using the pinned
root formulas in the next module.

This is the classical half-spin construction described in GLS3, §1.14.9(f),
used here for the point-group part of §1.15.2(a).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace Triality.SimplyConnected.Diagram.HalfSpin
open Theory.AlgebraicGroup
variable (k : Type*) [Field k] [CharP k 2]
abbrev Mask := Fin 4 → Bool
abbrev Fock := Mask → k

def flip (s : Mask) (i : Fin 4) : Mask := Function.update s i (!(s i))

def vectorAction (v : QuadraticSpace k) : Module.End k (Fock k) where
  toFun w s := ∑ i : Fin 4, (if s i then v.1 i else v.2 i) * w (flip s i)
  map_add' w z := by ext s; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a w := by
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def vectorMap : QuadraticSpace k →ₗ[k] Module.End k (Fock k) where
  toFun := vectorAction k
  map_add' v z := by
    apply LinearMap.ext
    intro w
    funext s
    simp only [vectorAction, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      Pi.add_apply, Prod.fst_add, Prod.snd_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases s i <;> simp [add_mul]
  map_smul' a v := by
    apply LinearMap.ext
    intro w
    funext s
    simp only [vectorAction, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      Pi.smul_apply, Prod.fst_smul, Prod.snd_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases s i <;> simp [mul_assoc]

theorem vectorMap_square (v : QuadraticSpace k) :
    vectorMap k v * vectorMap k v = algebraMap k (Module.End k (Fock k)) (quadraticForm k v) := by
  apply LinearMap.ext
  intro w
  funext s
  change (vectorAction k v) ((vectorAction k v) w) s = (quadraticForm k v) * w s
  simp only [vectorAction, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_four,
    quadraticForm, hyperbolicForm_apply]
  have hu0 := Function.update_eq_self 0 s
  have hu1 := Function.update_eq_self 1 s
  have hu2 := Function.update_eq_self 2 s
  have hu3 := Function.update_eq_self 3 s
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals
    simp [flip, Function.update_comm, h0, h1, h2, h3]
    ring_nf
    simp only [h0, h1, h2, h3] at hu0 hu1 hu2 hu3
    simp [CharTwo.two_eq_zero, hu0, hu1, hu2, hu3]

/-- The full sixteen-dimensional Clifford action in characteristic two. -/
def cliffordAction : CliffordAlgebra (quadraticForm k) →ₐ[k] Module.End k (Fock k) :=
  CliffordAlgebra.lift (quadraticForm k) ⟨vectorMap k, vectorMap_square k⟩

@[simp] theorem cliffordAction_ι (v : QuadraticSpace k) :
    cliffordAction k (CliffordAlgebra.ι (quadraticForm k) v) = vectorAction k v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Coordinates for the even half of the Clifford module. -/
def embedding : QuadraticSpace k →ₗ[k] Fock k where
  toFun v s := match s 0, s 1, s 2, s 3 with
    | true, true, true, true => v.1 0
    | true, true, false, false => v.1 1
    | true, false, true, false => v.1 2
    | false, true, true, false => v.1 3
    | false, false, false, false => v.2 0
    | false, false, true, true => v.2 1
    | false, true, false, true => v.2 2
    | true, false, false, true => v.2 3
    | _, _, _, _ => 0
  map_add' v w := by
    funext s
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3 <;> simp [h0, h1, h2, h3]
  map_smul' a v := by
    funext s
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3 <;> simp [h0, h1, h2, h3]

def firstMask : Fin 4 → Mask := ![
  ![true, true, true, true], ![true, true, false, false],
  ![true, false, true, false], ![false, true, true, false]]
def secondMask : Fin 4 → Mask := ![
  ![false, false, false, false], ![false, false, true, true],
  ![false, true, false, true], ![true, false, false, true]]

@[simp] theorem embedding_firstMask (v : QuadraticSpace k) (i : Fin 4) :
    embedding k v (firstMask i) = v.1 i := by fin_cases i <;> rfl
@[simp] theorem embedding_secondMask (v : QuadraticSpace k) (i : Fin 4) :
    embedding k v (secondMask i) = v.2 i := by fin_cases i <;> rfl

theorem embedding_injective : Function.Injective (embedding k) := by
  intro v w h
  apply Prod.ext <;> funext i
  · simpa using congrFun h (firstMask i)
  · simpa using congrFun h (secondMask i)

variable [IsAlgClosed k]
/-- Restricting the genuine Clifford action to the actual Spin point group. -/
def pointAction : Points k →* Module.End k (Fock k) :=
  (cliffordAction k).toMonoidHom.comp
    ((spinGroup (quadraticForm k)).subtype.comp (pointEquiv k).toMonoidHom)


end Triality.SimplyConnected.Diagram.HalfSpin
