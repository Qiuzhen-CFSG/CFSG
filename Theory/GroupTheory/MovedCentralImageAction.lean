module
public import Theory.GroupTheory.AutomizerEmbedding
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Conjugation on a moved subgroup through a central image

A homomorphism that is injective on a normalized subgroup identifies its
conjugation image with a subgroup of the original automizer. If U = [U,A]
and the kernel is central, every actor normalizing A and the image of U
already normalizes U: taking commutators removes the central kernel.

These transfers retain the literal maps in the unitary Rudvalis normalizer
calculation, Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section

open Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Restricting a homomorphism faithfully to a normalized subgroup preserves
its conjugation image, even if the homomorphism has an ambient kernel. -/
theorem card_mapped_conjugation_range_dvd_automizer
    (f : G →* H) (U C : Subgroup G) (hCU : C ≤ normalizer (U : Set G))
    (hf : Function.Injective (f.comp U.subtype))
    (hDE : C.map f ≤ normalizer (U.map f : Set H)) :
    Nat.card ((U.map f).normalizerMonoidHom.comp (inclusion hDE)).range ∣
      Nat.card U.normalizerMonoidHom.range := by
  let e : U ≃* U.map f := MulEquiv.ofBijective (f.subgroupMap U)
    ⟨fun x y h => hf (congrArg Subtype.val h), f.subgroupMap_surjective U⟩
  let a := (U.map f).normalizerMonoidHom.comp (inclusion hDE)
  let t := MulAut.congr e.symm
  have hr : a.range.map t.toMonoidHom ≤ U.normalizerMonoidHom.range := by
    rintro _ ⟨_,⟨d,rfl⟩,rfl⟩
    obtain ⟨c,hc,hcd⟩ := d.property
    refine ⟨⟨c,hCU hc⟩,?_⟩
    apply MulEquiv.ext
    intro u
    apply e.injective
    change e (U.normalizerMonoidHom ⟨c,hCU hc⟩ u) =
      e (e.symm (a d (e u)))
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change f (c*(u : G)*c⁻¹) = (d : H)*f u*(d : H)⁻¹
    rw [map_mul,map_mul,map_inv,hcd]
  have hd := card_dvd_of_le hr
  rw [←Nat.card_congr (a.range.equivMapOfInjective t.toMonoidHom t.injective).toEquiv] at hd
  exact hd
end Subgroup

namespace Subgroup
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

/-- Full commutator generation reflects normalization through a central kernel. -/
theorem normalizes_moved_of_central_image (f : G →* H) (U A C : Subgroup G)
    (hk : f.ker ≤ center G) (hm : U = ⁅U,A⁆)
    (hCA : C ≤ normalizer (A : Set G))
    (hCE : C.map f ≤ normalizer (U.map f : Set H)) :
    C ≤ normalizer (U : Set G) := by
  have hfull : ⁅(U.map f).comap f,A⁆ = U := by
    apply le_antisymm
    · rw [comap_map_eq]
      apply commutator_le.mpr
      intro w hw a ha
      obtain ⟨u,hu,z,hz,rfl⟩ := mem_sup_of_normal_right.mp hw
      have hzcomm : ⁅z,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_center_iff.mp (hk hz) a).symm)
      have hucomm : ⁅u,a⁆ ∈ U := hm.symm ▸ commutator_mem_commutator hu ha
      simpa only [commutatorElement_mul_left_eq_conj_mul,hzcomm,mul_one,
        mul_inv_cancel,one_mul] using hucomm
    · calc
        U = ⁅U,A⁆ := hm
        _ ≤ _ := commutator_mono (le_comap_map f U) le_rfl
  intro c hc
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [←hfull,map_commutator]
  have hA := mem_normalizer_iff_map_conj_eq.mp (hCA hc)
  have hU : ((U.map f).comap f).map (MulAut.conj c).toMonoidHom =
      (U.map f).comap f := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply mem_normalizer_iff.mpr
    intro u
    change f u ∈ U.map f ↔ f (c*u*c⁻¹) ∈ U.map f
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hCE (mem_map_of_mem f hc)) (f u)
  rw [hA]
  change ⁅((U.map f).comap f).map (MulAut.conj c).toMonoidHom,A⁆ = _
  rw [hU]
end Subgroup
