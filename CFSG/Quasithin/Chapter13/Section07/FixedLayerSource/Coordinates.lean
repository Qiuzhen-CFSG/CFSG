module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.NaturalCover
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.FixedSpaceTransport

/-!
# Coordinates for the actual natural fixed-layer action

A bijective linear natural cover of a normalized elementary abelian subgroup
identifies its literal conjugation action with the indicated matrix action.
Postcomposing the coordinates by a natural matrix conjugates that same actor
marking. These identities preserve the local flag while retaining the
original subgroup and quotient map.

Source: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G A : Type*} [Group G] [Group A]

theorem naturalCoordinates_linearAction
    (H N : Subgroup G) [IsElementaryAbelian 2 N]
    (hHN : H ≤ normalizer N) (q : H →* A)
    (δ : Representation (ZMod 2) A (Additive N))
    (p : Additive N →ₗ[ZMod 2] BinaryLinearThree.Vector) (hp : Function.Bijective p)
    (f : H →* SL)
    (ha : ∀ h w, p (δ (q h) w) = BinaryLinearThree.W (f h) (p w))
    (hc : ∀ (h : H) (w : Additive N), ((δ (q h) w).toMul : G) = h*w.toMul*(h:G)⁻¹) :
    linearAction H N hHN (naturalCoverCoordinates N p hp) = f := by
  apply MonoidHom.ext
  intro h
  apply slAut.injective
  apply MulEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := (naturalCoverCoordinates N p hp).surjective v
  apply (naturalCoverCoordinates N p hp).symm.injective
  apply Subtype.ext
  rw [linearAction_apply]
  have he : slAut (f h) (naturalCoverCoordinates N p hp w) =
      naturalCoverCoordinates N p hp (δ (q h) (Additive.ofMul w)).toMul := by
    apply Multiplicative.toAdd.injective
    rw [naturalCoverCoordinates_apply,slAut_apply,naturalCoverCoordinates_apply]
    exact (ha h (Additive.ofMul w)).symm
  rw [he,MulEquiv.symm_apply_apply]
  exact (hc h (Additive.ofMul w)).symm

theorem linearAction_postcompose
    (H N : Subgroup G) (hHN : H ≤ normalizer N) (e : N ≃* Model) (g : SL) :
    linearAction H N hHN (e.trans (slAut g)) =
      (MulAut.conj g).toMonoidHom.comp (linearAction H N hHN e) := by
  apply MonoidHom.ext
  intro h
  apply slAut.injective
  apply MulEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := (e.trans (slAut g)).surjective v
  apply (e.trans (slAut g)).symm.injective
  apply Subtype.ext
  rw [linearAction_apply]
  change (h : G)*w*(h:G)⁻¹ =
    ((e.trans (slAut g)).symm (slAut (g * linearAction H N hHN e h * g⁻¹)
      ((e.trans (slAut g)) w)) : G)
  rw [map_mul,map_mul,map_inv]
  simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply, MulEquiv.symm_trans_apply]
  exact (linearAction_apply H N hHN e h w).symm

end CFSG.Quasithin.Chapter13.Section07
