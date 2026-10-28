module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Linear
import Mathlib.Tactic

/-!
# Order-seven separation of the natural and dual actions

An explicit Singer matrix has order seven. Its equations on three basis
vectors force every intertwiner from the dual three-space to the natural
three-space to vanish. The same holds for two dual copies. Consequently
the induced operator on Hom(dual ⊕ dual,natural) has no fixed vector.

For any invariant subspace, displacement is injective and hence surjective
on that finite subspace. Solving displacement there proves that an element
fixed modulo the subspace already belongs to it. This gives the needed
fixed-point-free subquotient result without a semisimplicity assumption.
`HomImage` applies it to the literal unquotiented commutator homomorphism.

Source context: the faithfulness step in the proof of MS93 (4.5.4)(iv),
Meierfrankenfeld--Stellmacher (1993), printed p.899. This is a replacement
linear calculation, not an assertion that the printed pairing descends.
-/

@[expose] public section

open Matrix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer

/-- A Singer element in the same concrete SL₃(2) model as the source marking. -/
def singer : S := ⟨!![0,0,1; 1,0,1; 0,1,0], by decide⟩
private def e (i : Fin 3) : W := Pi.single i 1
private theorem si : singer⁻¹ = (⟨!![1,1,0; 0,0,1; 1,0,0], by decide⟩ : S) := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

/-- The specified Singer element has order seven. -/
theorem singer_order : orderOf singer = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem de : ∀ i : Fin 3, dual singer (e i) =
    if i = 0 then e 0 + e 1 else if i = 1 then e 2 else e 0 := by
  simp only [dual,si]
  decide +kernel

/-- Natural and dual three-spaces have no intertwiner for this order-seven actor. -/
theorem intertwiner_zero (f : W →ₗ[ZMod 2] W)
    (hf : ∀ v, f (dual singer v) = singer.val.mulVec (f v)) : f = 0 := by
  have hne20 : (2 : Fin 3) ≠ 0 := by decide
  have hne21 : (2 : Fin 3) ≠ 1 := by decide
  have h (i k : Fin 3) := congrFun (hf (e i)) k
  have h00 := h 0 0
  simp only [de] at h00
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h00
  have h01 := h 0 1
  simp only [de] at h01
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h01
  have h02 := h 0 2
  simp only [de] at h02
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h02
  have h10 := h 1 0
  simp only [de] at h10
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h10
  have h11 := h 1 1
  simp only [de] at h11
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h11
  have h12 := h 1 2
  simp only [de] at h12
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h12
  have h20 := h 2 0
  simp only [de] at h20
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h20
  have h21 := h 2 1
  simp only [de] at h21
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h21
  have h22 := h 2 2
  simp only [de] at h22
  norm_num [map_add, singer, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_two, vecHead, vecTail, hne20, hne21] at h22
  have hz (i k : Fin 3) : f (e i) k = 0 := by
    fin_cases i <;> fin_cases k
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h01 + h02 + h11 + h12 + h20 + h22
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h10 + h11 + h20 + h21 + h22
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h01 + h10 + h11 + h12 + h21 + h22
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h02 + h10 + h20 + h21
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h01 + h02 + h11 + h22
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h01 + h02 + h12 + h20
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h01 + h02 + h10 + h12 + h20
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h01 + h10 + h11 + h12 + h21
    · linear_combination (norm := (ring_nf; reduce_mod_char!; exact CharTwo.add_self_eq_zero _)) h00 + h01 + h02 + h11 + h12 + h22
  have he (v : W) : v = ∑ i : Fin 3, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  apply LinearMap.ext
  intro v
  change f v = 0
  rw [he v, map_sum]
  have hzero (i : Fin 3) : f (e i) = 0 := funext (hz i)
  simp [hzero]

/-- The same vanishing for the doubled dual source section. -/
theorem pair_intertwiner_zero (f : (W × W) →ₗ[ZMod 2] W)
    (hf : ∀ v : W × W, f (dual singer v.1, dual singer v.2) =
      singer.val.mulVec (f v)) : f = 0 := by
  have hleft : f.comp (LinearMap.inl (ZMod 2) W W) = 0 := by
    apply intertwiner_zero
    intro v
    simpa only [LinearMap.comp_apply, LinearMap.inl_apply, dual, Matrix.mulVec_zero]
      using hf (v,0)
  have hright : f.comp (LinearMap.inr (ZMod 2) W W) = 0 := by
    apply intertwiner_zero
    intro v
    simpa only [LinearMap.comp_apply, LinearMap.inr_apply, dual, Matrix.mulVec_zero]
      using hf (0,v)
  apply LinearMap.ext
  intro v
  have hv : v = (v.1,0) + (0,v.2) := by simp
  change f v = 0
  rw [hv, map_add]
  have hl := congrArg (fun l : W →ₗ[ZMod 2] W => l v.1) hleft
  have hr := congrArg (fun l : W →ₗ[ZMod 2] W => l v.2) hright
  exact (congrArg₂ (· + ·) hl hr).trans (zero_add 0)

/-- The natural conjugation operator on Hom(dual ⊕ dual,natural). -/
noncomputable def onHom : ((W × W) →ₗ[ZMod 2] W) ≃ₗ[ZMod 2] ((W × W) →ₗ[ZMod 2] W) :=
  let d := Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transpose singer⁻¹)
  LinearEquiv.arrowCongr (d.prodCongr d) (Matrix.SpecialLinearGroup.toLin' singer)

/-- The defining equivariance equation for the Hom operator. -/
theorem onHom_apply_dual (f : (W × W) →ₗ[ZMod 2] W) (v : W × W) :
    onHom f (dual singer v.1, dual singer v.2) = singer.val.mulVec (f v) := by
  let d := Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transpose singer⁻¹)
  change (Matrix.SpecialLinearGroup.toLin' singer)
    (f ((d.prodCongr d).symm ((d.prodCongr d) v))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Equality with the Hom action is the usual intertwining equation. -/
theorem onHom_eq_iff (f h : (W × W) →ₗ[ZMod 2] W) : onHom f = h ↔
    ∀ v : W × W, h (dual singer v.1, dual singer v.2) = singer.val.mulVec (f v) := by
  constructor
  · intro he v
    rw [← he]
    exact onHom_apply_dual f v
  · intro he
    apply LinearMap.ext
    intro u
    let d := Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transpose singer⁻¹)
    obtain ⟨v,rfl⟩ := (d.prodCongr d).surjective u
    exact (onHom_apply_dual f v).trans (he v).symm

/-- No nonzero Hom vector is fixed by the Singer operator. -/
theorem onHom_fixed (f : (W × W) →ₗ[ZMod 2] W) (hf : onHom f = f) : f = 0 := by
  apply pair_intertwiner_zero
  intro v
  let d := Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transpose singer⁻¹)
  have hv := congrArg (fun l : (W × W) →ₗ[ZMod 2] W => l ((d.prodCongr d) v)) hf
  change (Matrix.SpecialLinearGroup.toLin' singer) (f ((d.prodCongr d).symm ((d.prodCongr d) v))) =
    f ((d.prodCongr d) v) at hv
  rw [LinearEquiv.symm_apply_apply] at hv
  exact hv.symm

/-- Every invariant subquotient has no fixed vectors: solve the displacement
inside the finite invariant subspace and use injectivity in the whole space. -/
theorem mem_of_displacement_mem (N : Submodule (ZMod 2) ((W × W) →ₗ[ZMod 2] W))
    (hN : ∀ f ∈ N, onHom f ∈ N) (f : (W × W) →ₗ[ZMod 2] W)
    (hf : onHom f - f ∈ N) : f ∈ N := by
  let : Finite ((W × W) →ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : (W × W) →ₗ[ZMod 2] W => (f : W × W → W)) DFunLike.coe_injective
  let δ := onHom.toLinearMap - LinearMap.id
  have hδ : Function.Injective δ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro f hf
    exact onHom_fixed f (sub_eq_zero.mp hf)
  let d : N → N := fun n => ⟨δ n, N.sub_mem (hN n n.property) n.property⟩
  have hd : Function.Injective d := by
    intro n m h
    exact Subtype.ext (hδ (congrArg Subtype.val h))
  obtain ⟨n,hn⟩ := (Finite.surjective_of_injective hd) ⟨δ f,hf⟩
  have he : (n : (W × W) →ₗ[ZMod 2] W) = f := hδ (congrArg Subtype.val hn)
  exact he ▸ n.property

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer
