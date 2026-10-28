module
public import Theory.Representation.FourGroupMatrixCoordinates
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The two binary layer models at s = 1

The common actor is SL₂(2) × SL₂(2). On the lower layer it acts on
2 × 2 matrices by X ↦ a X bᵀ, the tensor of the two natural planes;
`tensorAction_outer` verifies this on pure tensors. On the upper layer
it acts separately on the two summands. The specified subgroup `nine`
is the product of the actual cubic rotation subgroups.

Cubic displacement is surjective on each required layer. Faithfulness
and tensor irreducibility use small kernel-checked calculations: the
nonzero matrices have two rank orbits, and one matrix unit generates
all four coordinate units. No automorphism group is enumerated.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53(1), 15.3.54(4), and the proof of 15.3.59, pp.1146 and 1150.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
open Matrix Subgroup
open scoped IsMulCommutative
abbrev PlaneActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev Actor := PlaneActor × PlaneActor
abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
abbrev SumVector := Plane × Plane
abbrev TensorVector := Multiplicative (Matrix (Fin 2) (Fin 2) (ZMod 2))

def rotation : PlaneActor := ⟨!![0, 1; 1, 1], by decide +kernel⟩
def cubic : Subgroup PlaneActor := zpowers rotation
def nine : Subgroup Actor := cubic.prod cubic

/-- The natural direct sum of the two binary planes. -/
def sumAction : Actor →* MulAut SumVector := by
  letI := FourGroupMatrixCoordinates.naturalAction
  let f := MulDistribMulAction.toMulAut PlaneActor Plane
  exact { toFun := fun a => (f a.1).prodCongr (f a.2)
          map_one' := by
            change (f 1).prodCongr (f 1) = 1
            rw [map_one]; rfl
          map_mul' := by
            intro a b
            change (f (a.1 * b.1)).prodCongr (f (a.2 * b.2)) = _
            simp only [map_mul]
            rfl }

/-- Matrix coordinates for the external tensor action. -/
def tensorAction : Actor →* MulAut TensorVector where
  toFun a :=
    { toFun := fun x => Multiplicative.ofAdd (a.1.val * x.toAdd * a.2.val.transpose)
      invFun := fun x => Multiplicative.ofAdd ((a.1⁻¹).val * x.toAdd * (a.2⁻¹).val.transpose)
      left_inv := by
        intro x
        change Multiplicative.ofAdd (_ * (_ * x.toAdd * _) * _) = x
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
        simp
      right_inv := by
        intro x
        change Multiplicative.ofAdd (_ * (_ * x.toAdd * _) * _) = x
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
        simp
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (_ * (x.toAdd + y.toAdd) * _) = _
        simp only [Matrix.mul_add, Matrix.add_mul]
        rfl }
  map_one' := by
    ext x i j
    simp
  map_mul' a b := by
    ext x i j
    change ((a.1.val * b.1.val) * x.toAdd * (a.2.val * b.2.val).transpose) i j =
      (a.1.val * (b.1.val * x.toAdd * b.2.val.transpose) * a.2.val.transpose) i j
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem card_planeActor : Nat.card PlaneActor = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_actor : Nat.card Actor = 36 := by
  rw [Nat.card_prod, card_planeActor]

theorem rotation_order : orderOf rotation = 3 := by
  exact orderOf_eq_prime (by decide +kernel : rotation ^ 3 = 1) (by decide +kernel)

theorem card_nine : Nat.card nine = 9 := by
  change Nat.card (cubic.prod cubic) = 9
  rw [Nat.card_congr (Subgroup.prodEquiv cubic cubic).toEquiv, Nat.card_prod]
  change Nat.card (zpowers rotation) * Nat.card (zpowers rotation) = 9
  rw [Nat.card_zpowers, rotation_order]

theorem tensorAction_apply (a : Actor) (x : TensorVector) :
    tensorAction a x = Multiplicative.ofAdd (a.1.val * x.toAdd * a.2.val.transpose) := rfl

theorem tensorAction_outer (a : Actor) (v w : Fin 2 → ZMod 2) :
    tensorAction a (Multiplicative.ofAdd (Matrix.vecMulVec v w)) =
      Multiplicative.ofAdd (Matrix.vecMulVec (a.1.val *ᵥ v) (a.2.val *ᵥ w)) := by
  change Multiplicative.ofAdd (a.1.val * Matrix.vecMulVec v w * a.2.val.transpose) = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose]

theorem tensor_displacement : ∀ x : TensorVector,
    ∃ w : TensorVector, tensorAction (rotation, 1) w * w⁻¹ = x := by
  decide +kernel

theorem sum_displacement : ∀ x : SumVector,
    ∃ w : SumVector, sumAction (rotation, rotation) w * w⁻¹ = x := by
  decide +kernel

theorem tensorAction_injective : Function.Injective tensorAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have h : ∀ a : Actor, (∀ x : TensorVector, tensorAction a x = x) → a = 1 := by
    decide +kernel
  exact h a (fun x => MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) x)

theorem sumAction_injective : Function.Injective sumAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have h : ∀ a : Actor, (∀ x : SumVector, sumAction a x = x) → a = 1 := by
    decide +kernel
  exact h a (fun x => MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) x)

private def seed : TensorVector := Multiplicative.ofAdd !![1, 0; 0, 0]
private def full : TensorVector := Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
private def swap : PlaneActor := ⟨!![0, 1; 1, 0], by decide +kernel⟩
private def shear : PlaneActor := ⟨!![1, 1; 0, 1], by decide +kernel⟩

private theorem tensor_orbits : ∀ x : TensorVector, x ≠ 1 →
    ∃ a : Actor, tensorAction a x = seed ∨ tensorAction a x = full := by
  decide +kernel

private theorem seed_from_full :
    tensorAction (1, swap) (tensorAction (shear, 1) full * full) = seed := by
  decide +kernel

private theorem tensor_basis_expansion : ∀ x : TensorVector,
    x = seed ^ (x.toAdd 0 0).val *
      tensorAction (1, swap) seed ^ (x.toAdd 0 1).val *
      tensorAction (swap, 1) seed ^ (x.toAdd 1 0).val *
      tensorAction (swap, swap) seed ^ (x.toAdd 1 1).val := by
  decide +kernel

/-- The full product actor is irreducible on the binary tensor space.
The two nonzero matrix-rank orbits reduce the proof to one matrix unit. -/
theorem tensor_irreducible (D : Subgroup TensorVector)
    (hinvariant : ∀ (a : Actor) (x : TensorVector), x ∈ D → tensorAction a x ∈ D) :
    D = ⊥ ∨ D = ⊤ := by
  by_cases hD : D = ⊥
  · exact Or.inl hD
  right
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hx := x.property
  obtain ⟨a, ha | ha⟩ := tensor_orbits x (fun h => hx1 (Subtype.ext h))
  · have hs : seed ∈ D := ha ▸ hinvariant a x hx
    apply top_unique
    intro v _
    rw [tensor_basis_expansion v]
    exact D.mul_mem (D.mul_mem (D.mul_mem (D.pow_mem hs _)
      (D.pow_mem (hinvariant (1, swap) seed hs) _))
      (D.pow_mem (hinvariant (swap, 1) seed hs) _))
      (D.pow_mem (hinvariant (swap, swap) seed hs) _)
  · have hf : full ∈ D := ha ▸ hinvariant a x hx
    have hs : seed ∈ D := seed_from_full ▸
      hinvariant (1, swap) _ (D.mul_mem (hinvariant (shear, 1) full hf) hf)
    apply top_unique
    intro v _
    rw [tensor_basis_expansion v]
    exact D.mul_mem (D.mul_mem (D.mul_mem (D.pow_mem hs _)
      (D.pow_mem (hinvariant (1, swap) seed hs) _))
      (D.pow_mem (hinvariant (swap, 1) seed hs) _))
      (D.pow_mem (hinvariant (swap, swap) seed hs) _)

/-- Every automorphism of an elementary binary group is canonically linear.
This identifies the full automorphism normalizer used here with GL(B),
without choosing a basis or changing its embedded subgroup. -/
noncomputable def binaryAutEquiv (E : Type*) [Group E] [IsElementaryAbelian 2 E] :
    MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) := by
  exact
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
