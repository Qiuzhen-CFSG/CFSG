module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic

open Subgroup Stellmacher
/-!
# Cubic displacement in the natural orthogonal module

A cubic matrix on each binary plane has invertible displacement. The exact
coordinate compatibility therefore writes every vector as a commutator with
an element of any subgroup whose action image contains the actor residual.
The cubic actor belongs to that residual because its order divides three.

Source: Aschbacher–Smith, Lemma 15.3.7, printed p.1122 (PDF p.1139).
-/

namespace CFSG.Quasithin.Chapter15.Section03

private def cubicPlane : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩
private def cubicActor : OrthogonalActor := ⟨fun _ => cubicPlane, 1⟩

private theorem cubicActor_cube : cubicActor ^ 3 = 1 := by
  have h : cubicPlane ^ 3 = 1 := by decide +kernel
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_succ, cubicActor] using h
  · rfl

private theorem cubic_displacement : letI := orthogonalAction
    ∀ v : OrthogonalVector, cubicActor • (cubicActor • v) * (cubicActor • v)⁻¹ = v := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  have h : ∀ v : OrthogonalPlaneVector,
      cubicPlane • (cubicPlane • v) * (cubicPlane • v)⁻¹ = v := by decide +kernel
  let _ := orthogonalAction
  intro v
  funext i
  simpa only [cubicActor, RegularWreathProduct.functionModule_smul_apply,
    inv_one, one_mul, Pi.mul_apply, Pi.inv_apply] using h (v i)

private theorem cubic_mem_residual {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (x : X) (hx : x ∈ H) (h3 : x ^ 3 = 1) :
    x ∈ twoResidualAmbient H := by
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  change (⟨x,hx⟩ : H) ∈ twoResidualSubgroup H
  rw [twoResidualSubgroup, Subgroup.mem_sInf]
  rintro N ⟨hN,n,hn⟩
  let _ := hN
  have hp : IsPGroup 2 (H ⧸ N) := IsPGroup.iff_card.mpr
    ⟨n, by simpa only [← Subgroup.index_eq_card] using hn⟩
  apply (QuotientGroup.eq_one_iff (N := N) (⟨x,hx⟩ : H)).mp
  have hc : (QuotientGroup.mk' N (⟨x,hx⟩ : H)) ^ 3 = 1 := by
    rw [← map_pow]
    have hs : (⟨x,hx⟩ : H) ^ 3 = 1 := Subtype.ext h3
    rw [hs, map_one]
  obtain ⟨k,hk⟩ := hp.exists_orderOf_dvd_pow (QuotientGroup.mk' N (⟨x,hx⟩ : H))
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
    hk (orderOf_dvd_of_pow_eq_one hc)

private theorem commutator_of_image {G : Type*} [Group G] [Finite G]
    (M V Y : Subgroup G) (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (hc : cubicActor ∈ (Y.subgroupOf M).map d.actor) : ⁅V,Y⁆ = V := by
  let _ := orthogonalAction
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp (hYM.trans d.normalizes)
  · intro v hv
    obtain ⟨y,hy,hey⟩ := hc
    let w : V := d.coordinates.symm (cubicActor • d.coordinates ⟨v,hv⟩)
    have hn : (y : G) ∈ normalizer (V : Set G) := d.normalizes y.property
    let z : V := V.normalizerMonoidHom ⟨y,hn⟩ w * w⁻¹
    have hz : z = ⟨v,hv⟩ := by
      apply d.coordinates.injective
      dsimp only [z]
      rw [map_mul, map_inv, d.compatible, hey]
      dsimp only [w]
      rw [d.coordinates.apply_symm_apply, cubic_displacement]
    have hval : (y : G) * (w : G) * (y : G)⁻¹ * (w : G)⁻¹ = v :=
      congrArg V.subtype hz
    rw [← hval, commutator_comm]
    exact commutator_mem_commutator hy w.property

/-- The residual image forces the full module commutator, using the specified
coordinate action rather than an abstract isomorphism of actors. -/
public theorem NaturalOrthogonalAction.commutator_eq_of_residual_image
    {G : Type*} [Group G] [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (Y : Subgroup G) (hYM : Y ≤ M)
    (himage : (Y.subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    ⁅V,Y⁆ = V := by
  apply commutator_of_image M V Y d hYM
  rw [himage]
  exact cubic_mem_residual ⊤ cubicActor (mem_top _) cubicActor_cube

end CFSG.Quasithin.Chapter15.Section03
