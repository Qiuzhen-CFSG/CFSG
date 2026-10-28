module

public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves

/-!
# Clifford coordinates for the Geck D4 comparison

The 24 root coordinates are sent to the literal products of signed isotropic
vectors defining the Spin root curves. A simple Cartan coordinate is sent to
the commutator of its positive and negative root bivectors. This specifies a
linear map from the full 28-coordinate Geck space into the Clifford algebra,
with the same vertex numbering and both root signs as the pinned Spin model.

`Intertwines` compares the actual Geck matrix action with Clifford conjugation
on these coordinates. It is preserved by products and inverses. Injectivity of
the coordinate map detects the Geck matrix. The injectivity, faithfulness of
conjugation on its image, and the signed simple-root identities are separate
mathematical obligations; they are not asserted by these definitions.

Sources: GLS3, §§1.12–1.14, especially the adjoint construction in 1.14.9(c),
and §2.7 (`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open RootPairing.SimpleGeckGroup
open scoped Matrix

/-- The literal Cartan-plus-root index of the standard Geck matrices. -/
abbrev Index := (typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)
local instance indexDecidableEq : DecidableEq Index := instDecidableEqSum

/-- The full Geck coordinate space after extension of coefficients. -/
abbrev Coordinates (k : Type*) := Index → k
/-- The Clifford algebra of the fixed four-hyperbolic-plane model. -/
abbrev Clifford (k : Type*) [Field k] := CliffordAlgebra (quadraticForm k)

variable (k : Type*) [Field k]

/-- The simple Cartan vector, with the commutator orientation of the root pair. -/
def cartanBivector (i : Fin 4) : Clifford k :=
  rootBivector k (simpleRoot i) * rootBivector k (negativeSimpleRoot i) -
    rootBivector k (negativeSimpleRoot i) * rootBivector k (simpleRoot i)

/-- The proposed Clifford realization of each literal Geck basis vector. -/
def basisImage : Index → Clifford k
  | Sum.inl i => cartanBivector k ((typeDRootPairing_baseEquiv 2).symm i)
  | Sum.inr r => rootBivector k r

/-- Linear extension of the explicitly specified Cartan and root images. -/
def embedding : Coordinates k →ₗ[k] Clifford k where
  toFun v := ∑ i, v i • basisImage k i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem embedding_single (i : Index) (a : k) :
    embedding k (Pi.single i a) = a • basisImage k i := by
  classical
  change (∑ j, (Pi.single i a : Coordinates k) j • basisImage k j) = _
  simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The concrete Geck matrix group over the ambient coefficient field. -/
abbrev SplitPoints := Carrier (typeDRootPairing_base 2) k

/-- Its tautological action on all 28 coordinates. -/
def matrixAction : SplitPoints k →* Module.End k (Coordinates k) where
  toFun g := Matrix.mulVecLin g.val.val
  map_one' := Matrix.mulVecLin_one
  map_mul' _ _ := Matrix.mulVecLin_mul _ _

@[simp] theorem matrixAction_apply (g : SplitPoints k) (v : Coordinates k) :
    matrixAction k g v = g.val.val *ᵥ v := rfl

theorem matrixAction_injective : Function.Injective (matrixAction k) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  exact congrArg DFunLike.coe he

variable [IsAlgClosed k]

/-- The actual Spin conjugation representation on the full Clifford algebra. -/
def pointConjugation : Points k →* Module.End k (Clifford k) where
  toFun g := LinearMap.mulLeftRight k
    ((pointEquiv k g : Clifford k), (pointEquiv k g⁻¹ : Clifford k))
  map_one' := by
    ext c
    simp [LinearMap.mulLeftRight]
  map_mul' g h := by
    ext c
    simp [LinearMap.mulLeftRight, mul_assoc]

@[simp] theorem pointConjugation_apply (g : Points k) (c : Clifford k) :
    pointConjugation k g c =
      (pointEquiv k g : Clifford k) * c * (pointEquiv k g⁻¹ : Clifford k) := rfl


/-- Equality of the actual Clifford and Geck actions on the comparison space. -/
def Intertwines (g : SplitPoints k) (x : Points k) : Prop :=
  ∀ v, pointConjugation k x (embedding k v) = embedding k (matrixAction k g v)

/-- The identity elements have compatible actions. -/
theorem intertwines_one : Intertwines k 1 1 := by
  intro v
  simp only [map_one, Module.End.one_apply]

/-- Compatibility is preserved by products of the actual group elements. -/
theorem Intertwines.mul {g h : SplitPoints k} {x y : Points k}
    (hx : Intertwines k g x) (hy : Intertwines k h y) :
    Intertwines k (g * h) (x * y) := by
  intro v
  calc
    pointConjugation k (x * y) (embedding k v) =
        pointConjugation k x (pointConjugation k y (embedding k v)) :=
      congrArg (fun F : Module.End k (Clifford k) => F (embedding k v))
        ((pointConjugation k).map_mul x y)
    _ = pointConjugation k x (embedding k (matrixAction k h v)) :=
      congrArg (pointConjugation k x) (hy v)
    _ = embedding k (matrixAction k g (matrixAction k h v)) := hx _
    _ = embedding k (matrixAction k (g * h) v) :=
      congrArg (fun F : Module.End k (Coordinates k) => embedding k (F v))
        ((matrixAction k).map_mul g h).symm

/-- Compatibility is preserved by inverses of the actual group elements. -/
theorem Intertwines.inv {g : SplitPoints k} {x : Points k}
    (hx : Intertwines k g x) : Intertwines k g⁻¹ x⁻¹ := by
  intro v
  have h := congrArg (pointConjugation k x⁻¹) (hx (matrixAction k g⁻¹ v))
  have hg : matrixAction k g (matrixAction k g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hxi (w : Clifford k) : pointConjugation k x⁻¹ (pointConjugation k x w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hg, hxi] at h
  exact h.symm

/-- Injectivity of the comparison embedding detects the literal Geck matrix. -/
theorem Intertwines.geck_unique (hι : Function.Injective (embedding k))
    {g h : SplitPoints k} {x : Points k}
    (hg : Intertwines k g x) (hh : Intertwines k h x) : g = h := by
  apply matrixAction_injective k
  apply LinearMap.ext
  intro v
  exact hι ((hg v).symm.trans (hh v))

end Triality.BinaryDegree.CarrierTransport.GeckSpin
