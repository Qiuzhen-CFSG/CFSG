module
public import Theory.Representation.MathieuCodeRestriction
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Native M24 point-stabilizer tensor induction

For a point-restriction intertwiner f from an extended module W to V,
transport f to each of the 24 point fibers. The bilinear orbit sum
δᵢ ⊗ w ↦ σ(gᵢ) f(τ(gᵢ⁻¹)w) is independent of the transporter because
f intertwines the literal M23 stabilizer action. It gives a map from the
native permutation action tensored with W to σ. Its value at δ₀ ⊗ w
recovers f(w), so nonzero point maps remain nonzero. A fixed point vector
gives the native permutation source by taking the trivial coefficient line.

This is Frobenius reciprocity in the actual Golay coordinate convention;
no semisimple restriction or coset-marking substitution is used.
Source application: Aschbacher–Smith, B.4.2 and H.13.1; Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, M24 paragraph.
-/

public section
open Representation Sporadic.Mathieu MathieuCode
open scoped TensorProduct
noncomputable section
namespace Representation.MathieuSmall.M24SmallFF.PointInduction
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

private def liftPoint (x : Fin 24) : M24 :=
  Classical.choose (MulAction.exists_smul_eq M24 (0 : Fin 24) x)
private theorem liftPoint_spec (x : Fin 24) : liftPoint x • (0 : Fin 24) = x :=
  Classical.choose_spec (MulAction.exists_smul_eq M24 (0 : Fin 24) x)

private def fiberMap (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding))
    (i : Fin 24) : W →ₗ[ZMod 2] V :=
  σ (liftPoint i) ∘ₗ f.toLinearMap ∘ₗ τ (liftPoint i)⁻¹

private theorem fiberMap_eq (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding))
    (g : M24) (i : Fin 24) (hi : g • (0 : Fin 24) = i) (w : W) :
    fiberMap τ σ f i w = σ g (f (τ g⁻¹ w)) := by
  have hs : (liftPoint i)⁻¹ * g ∈ pointEmbedding.range := by
    rw [pointEmbedding_range]
    change ((liftPoint i)⁻¹ * g) • (0 : Fin 24) = 0
    rw [mul_smul,hi]
    exact (congrArg (fun x => (liftPoint i)⁻¹ • x) (liftPoint_spec i).symm).trans
      (inv_smul_smul (liftPoint i) (0 : Fin 24))
  obtain ⟨h,hh⟩ := hs
  have h' := LinearMap.congr_fun (f.isIntertwining' h) (τ g⁻¹ w)
  change f (τ (pointEmbedding h) (τ g⁻¹ w)) =
    σ (pointEmbedding h) (f (τ g⁻¹ w)) at h'
  rw [hh, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel, mul_one] at h'
  change σ (liftPoint i) (f (τ (liftPoint i)⁻¹ w)) = _
  rw [h', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

private theorem fiberMap_equivariant (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding))
    (g : M24) (i : Fin 24) (w : W) :
    fiberMap τ σ f (g • i) (τ g w) = σ g (fiberMap τ σ f i w) := by
  rw [fiberMap_eq τ σ f (g * liftPoint i) (g • i) (by rw [mul_smul,liftPoint_spec])]
  simp only [mul_inv_rev,map_mul,Module.End.mul_apply,Representation.inv_self_apply]
  rfl

private def fiberBilinear (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding)) :
    Full →ₗ[ZMod 2] W →ₗ[ZMod 2] V where
  toFun a := ∑ i : Fin 24, a i • fiberMap τ σ f i
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [mul_smul,Finset.smul_sum]

private def tensorLinear (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding)) :
    Full ⊗[ZMod 2] W →ₗ[ZMod 2] V := TensorProduct.lift (fiberBilinear τ σ f)

private theorem tensorLinear_tmul (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding))
    (a : Full) (w : W) :
    tensorLinear τ σ f (a ⊗ₜ w) = ∑ i : Fin 24, a i • fiberMap τ σ f i w := by
  simp [tensorLinear,fiberBilinear]

def tensorInduce (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding)) :
    (fullRepresentation.tprod τ).IntertwiningMap σ where
  toLinearMap := tensorLinear τ σ f
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro w
    simp only [tprod_apply]
    change (∑ i : Fin 24, a (g.val.symm i) • fiberMap τ σ f i (τ g w)) =
      σ g (∑ i : Fin 24, a i • fiberMap τ σ f i w)
    rw [map_sum]
    simp only [map_smul]
    have he := (Equiv.sum_comp g.val
      (fun i : Fin 24 => a (g.val.symm i) • fiberMap τ σ f i (τ g w))).symm
    apply he.trans
    apply Finset.sum_congr rfl
    intro i hi
    simp only [_root_.Equiv.symm_apply_apply]
    rw [show g.val i = g • i from rfl, fiberMap_equivariant]

theorem tensorInduce_at_base (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding)) (w : W) :
    tensorInduce τ σ f ((Pi.single 0 1 : Full) ⊗ₜ w) = f w := by
  change tensorLinear τ σ f _ = _
  rw [tensorLinear_tmul]
  simp only [Pi.single_apply, ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [fiberMap_eq τ σ f 1 0 (one_smul _ _) w]
  simp

theorem tensorInduce_ne_zero (τ : Representation (ZMod 2) M24 W)
    (σ : Representation (ZMod 2) M24 V)
    (f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding)) (hf : f ≠ 0) :
    tensorInduce τ σ f ≠ 0 := by
  intro hz
  apply hf
  ext w
  have he := congrArg (fun k : (fullRepresentation.tprod τ).IntertwiningMap σ =>
    k ((Pi.single 0 1 : Full) ⊗ₜ w)) hz
  rw [tensorInduce_at_base] at he
  exact he
end Representation.MathieuSmall.M24SmallFF.PointInduction
namespace Representation.MathieuSmall.M24SmallFF.PointInduction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem permutation_map_of_point_fixed (σ : Representation (ZMod 2) M24 V)
    (hv : Representation.invariants (σ.comp pointEmbedding) ≠ ⊥) :
    ∃ f : fullRepresentation.IntertwiningMap σ, f ≠ 0 := by
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp hv
  let τ := Representation.trivial (ZMod 2) M24 (ZMod 2)
  let f : IntertwiningMap (τ.comp pointEmbedding) (σ.comp pointEmbedding) := {
    toLinearMap := LinearMap.toSpanSingleton (ZMod 2) V v
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change a • v = σ (pointEmbedding g) (a • v)
      rw [map_smul]
      exact congrArg (a • ·) (hv g).symm }
  let j : fullRepresentation.IntertwiningMap (fullRepresentation.tprod τ) := {
    toLinearMap := (TensorProduct.mk (ZMod 2) Full (ZMod 2)).flip 1
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change fullRepresentation g a ⊗ₜ[ZMod 2] (1 : ZMod 2) =
        TensorProduct.map (fullRepresentation g) (τ g) (a ⊗ₜ 1)
      rw [TensorProduct.map_tmul]
      rfl }
  refine ⟨(tensorInduce τ σ f).comp j,?_⟩
  intro hz
  have he := congrArg (fun k : fullRepresentation.IntertwiningMap σ => k (Pi.single 0 1)) hz
  change tensorInduce τ σ f ((Pi.single 0 1 : Full) ⊗ₜ (1 : ZMod 2)) = 0 at he
  rw [tensorInduce_at_base] at he
  have hvz : v = 0 := by simpa [f] using he
  exact hv0 hvz
end Representation.MathieuSmall.M24SmallFF.PointInduction
