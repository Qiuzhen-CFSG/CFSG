module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Abel

/-!
# The full seed centralizer acting on its natural fixed space

Let s be the literal max1 kernel seed `(xy)^14` in the original matrix
carrier. Every element of C_Model(s) preserves ker(s - 1) on the natural
112-dimensional binary column module. Restricting to this fixed space gives
`fixedAction`, with the original full centralizer as its domain.

The seed belongs to the action kernel. Every kernel element has displacement
mapping the natural module into the fixed space, which the whole kernel fixes
pointwise. Products of two such displacements vanish; consequently the kernel
is elementary abelian. The kernel-image formula reduces the centralizer order
to two independent finite bounds. Neither numerical bound is asserted here.

This construction does not use the quotient ker(s - 1) / im(s - 1), identify
an ambient centralizer with a local word subgroup, or require simplicity.
Source motivation: GLS3, Table 5.3i, printed p.270, records E₂¹¹.(M₂₂.2).
The literal word and checked matrix provenance are in `Cardinality.Subgroup`
and `Cardinality.LocalOrder.KernelCount`; the table supplies no proof premise.
-/

set_option maxRecDepth 2048

@[expose] public section

namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder
open Cardinality

/-- The original binary column module, with left matrix multiplication. -/
abbrev NaturalModule := Fin 112 → ZMod 2

/-- The full centralizer of the literal seed in the original matrix carrier. -/
abbrev Centralizer := ambientSeedCentralizer matrixA_mul_self matrixB_pow_four

/-- The actual max1 word, coerced into the ambient model. -/
def seed : Model := (localKernelSeed matrixA_mul_self matrixB_pow_four : Model)

/-- The seed regarded as an element of its full centralizer. -/
def markedSeed : Centralizer :=
  ⟨seed, by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    rfl⟩

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

/-- The certified kernel word squares to the identity. -/
theorem markedSeed_sq : markedSeed * markedSeed = 1 := by
  apply Subtype.ext
  exact congrArg (fun z : max1Subgroup matrixA_mul_self matrixB_pow_four => (z : Model))
    (KernelCount.basis_square matrixA_mul_self matrixB_pow_four 0)

/-- Every actor in the full centralizer commutes with its marked seed. -/
theorem markedSeed_commute (c : Centralizer) : markedSeed * c = c * markedSeed := by
  exact Subtype.ext (c.property _ (Set.mem_singleton _))

/-- The faithful natural representation of the entire ambient centralizer. -/
def naturalAction : Representation (ZMod 2) Centralizer NaturalModule :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (toMatrix.comp Centralizer.subtype)

/-- The natural action uses the original matrices on columns. -/
theorem naturalAction_apply (c : Centralizer) (v : NaturalModule) :
    naturalAction c v = Matrix.mulVec (toMatrix (c : Model)) v := rfl

/-- Restriction to the full centralizer retains matrix faithfulness. -/
theorem naturalAction_injective : Function.Injective naturalAction := by
  intro c d h
  apply Subtype.ext
  apply toMatrix_injective
  exact Matrix.toLinAlgEquiv'.injective h

/-- The linear displacement s - 1 of the literal seed. -/
def displacement : Module.End (ZMod 2) NaturalModule := naturalAction markedSeed - 1

/-- The displacement in the original matrix coordinates. -/
theorem displacement_apply (v : NaturalModule) :
    displacement v = Matrix.mulVec (toMatrix seed) v - v := rfl

/-- The displacement of an involution has square zero in characteristic two. -/
theorem displacement_sq : displacement * displacement = 0 := by
  have ha : naturalAction markedSeed * naturalAction markedSeed = 1 := by
    rw [← map_mul, markedSeed_sq, map_one]
  have hn : -(1 : Module.End (ZMod 2) NaturalModule) = 1 := by
    ext v i
    exact CharTwo.neg_eq _
  have hs (f : Module.End (ZMod 2) NaturalModule) : f + f = 0 := by
    ext v i
    exact CharTwo.add_self_eq_zero _
  rw [displacement, sub_eq_add_neg, hn, add_mul, mul_add, mul_add,
    mul_one, one_mul, one_mul, ha]
  rw [add_assoc, ← add_assoc (naturalAction markedSeed), hs, zero_add, hs]

/-- The displacement commutes with every full-centralizer actor. -/
theorem displacement_commute (c : Centralizer) :
    displacement * naturalAction c = naturalAction c * displacement := by
  dsimp only [displacement]
  rw [sub_mul, mul_sub, one_mul, mul_one, ← map_mul, ← map_mul,
    markedSeed_commute c]

/-- The actual fixed subspace ker(s - 1), without a chosen coordinate basis. -/
def fixedVectors : Submodule (ZMod 2) NaturalModule := LinearMap.ker displacement

/-- Membership means fixation by the literal seed matrix. -/
theorem mem_fixedVectors_iff (v : NaturalModule) :
    v ∈ fixedVectors ↔ Matrix.mulVec (toMatrix seed) v = v := by
  change displacement v = 0 ↔ _
  rw [displacement_apply, sub_eq_zero]

/-- The seed displacement takes values in the fixed subspace. -/
theorem displacement_mem_fixedVectors (v : NaturalModule) :
    displacement v ∈ fixedVectors := by
  change (displacement * displacement) v = 0
  rw [displacement_sq, LinearMap.zero_apply]

/-- All full-centralizer actors preserve the fixed subspace. -/
theorem fixedVectors_invariant (c : Centralizer) :
    fixedVectors ≤ fixedVectors.comap (naturalAction c) := by
  intro v hv
  change displacement (naturalAction c v) = 0
  have he := LinearMap.congr_fun (displacement_commute c) v
  change displacement (naturalAction c v) = naturalAction c (displacement v) at he
  rw [he, show displacement v = 0 from hv, map_zero]

/-- The natural representation restricted to the seed fixed space. -/
def fixedRepresentation : Representation (ZMod 2) Centralizer fixedVectors :=
  naturalAction.subrepresentation fixedVectors fixedVectors_invariant

/-- The induced homomorphism to invertible endomorphisms of the fixed space. -/
def fixedAction : Centralizer →* (Module.End (ZMod 2) fixedVectors)ˣ :=
  fixedRepresentation.asGroupHom

/-- The restricted action agrees with the original column action. -/
theorem fixedAction_apply (c : Centralizer) (v : fixedVectors) :
    ((fixedAction c : Module.End (ZMod 2) fixedVectors) v : NaturalModule) =
      naturalAction c v := rfl

/-- The kernel consists precisely of pointwise fixers of the full fixed space. -/
theorem mem_fixedAction_ker_iff (c : Centralizer) :
    c ∈ fixedAction.ker ↔ ∀ v ∈ fixedVectors, naturalAction c v = v := by
  constructor
  · intro hc v hv
    have h := congrArg (fun u : (Module.End (ZMod 2) fixedVectors)ˣ =>
      ((u : Module.End (ZMod 2) fixedVectors) ⟨v, hv⟩ : NaturalModule)) hc
    exact h
  · intro hc
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact Subtype.ext (hc v v.property)

/-- The literal seed acts trivially on its fixed space. -/
theorem markedSeed_mem_fixedAction_ker : markedSeed ∈ fixedAction.ker := by
  apply (mem_fixedAction_ker_iff _).mpr
  intro v hv
  exact sub_eq_zero.mp (show naturalAction markedSeed v - v = 0 from hv)

attribute [local irreducible] naturalAction displacement fixedRepresentation fixedAction

/-- A kernel actor differs from the identity by a map into the fixed space. -/
theorem kernel_displacement_mem_fixedVectors (c : fixedAction.ker) (v : NaturalModule) :
    naturalAction c.val v - v ∈ fixedVectors := by
  change displacement (naturalAction c.val v - v) = 0
  rw [map_sub]
  have he := LinearMap.congr_fun (displacement_commute c.val) v
  change displacement (naturalAction c.val v) = naturalAction c.val (displacement v) at he
  rw [he, (mem_fixedAction_ker_iff c.val).mp c.property _
    (displacement_mem_fixedVectors v), sub_self]

/-- Two kernel displacements have zero composite. -/
theorem kernel_displacement_mul (c d : fixedAction.ker) :
    (naturalAction c.val - 1) * (naturalAction d.val - 1) = 0 := by
  apply LinearMap.ext
  intro v
  change naturalAction c.val (naturalAction d.val v - v) -
    (naturalAction d.val v - v) = 0
  rw [(mem_fixedAction_ker_iff c.val).mp c.property _
    (kernel_displacement_mem_fixedVectors d v), sub_self]

private theorem kernel_action_mul (c d : fixedAction.ker) :
    naturalAction c.val * naturalAction d.val =
      naturalAction c.val + naturalAction d.val - 1 := by
  have hc := kernel_displacement_mul c d
  simp only [sub_mul, mul_sub, mul_one, one_mul] at hc
  calc
    _ = (naturalAction c.val - 1) + naturalAction d.val :=
      sub_eq_iff_eq_add.mp (sub_eq_zero.mp hc)
    _ = _ := by abel

/-- The full fixed-space action kernel is commutative. -/
theorem fixedAction_kernel_mul_comm (c d : fixedAction.ker) : c * d = d * c := by
  apply Subtype.ext
  apply naturalAction_injective
  change naturalAction (c.val * d.val) = naturalAction (d.val * c.val)
  rw [map_mul, map_mul, kernel_action_mul, kernel_action_mul,
    add_comm (naturalAction c.val)]

/-- Every member of the full fixed-space action kernel squares to one. -/
theorem fixedAction_kernel_sq (c : fixedAction.ker) : c ^ 2 = 1 := by
  apply Subtype.ext
  apply naturalAction_injective
  have hs : naturalAction c.val + naturalAction c.val = 0 := by
    ext v i
    exact CharTwo.add_self_eq_zero _
  have hn : -(1 : Module.End (ZMod 2) NaturalModule) = 1 := by
    ext v i
    exact CharTwo.neg_eq _
  change naturalAction (c.val ^ 2) = naturalAction 1
  rw [map_pow, map_one, pow_two, kernel_action_mul, hs, zero_sub, hn]

/-- The full fixed-space action kernel is an elementary abelian two-group. -/
theorem fixedAction_kernel_elementary : IsElementaryAbelian 2 fixedAction.ker := by
  refine {
    toIsMulCommutative := ⟨⟨fixedAction_kernel_mul_comm⟩⟩
    exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fixedAction_kernel_sq

/-- The full centralizer order is the product of the kernel and image orders. -/
theorem card_centralizer_eq_kernel_mul_image :
    Nat.card Centralizer = Nat.card fixedAction.ker * Nat.card fixedAction.range := by
  rw [← fixedAction.ker.card_mul_index, Subgroup.index_ker]

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder
