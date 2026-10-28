module
public import Theory.GroupAction.CoprimeCentralizerLift
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# Centralizers in the normalizer action

Coprime fixed-point lifting through the embedded center identifies the
centralizer of an actor inside the inner automorphisms with the image of
its actual centralizer in the original subgroup. The equality persists
when that subgroup is supplemented by elements fixing the actor.

This is the centralizer transport in Aschbacher--Smith, proof of 12.6.26,
printed p.832. Only the center, not the whole subgroup, must have order
coprime to the actor.
-/

public section
open Subgroup
namespace Subgroup.NormalizerAction
variable {G : Type*} [Group G] [Finite G]

/-- The inner centralizer lifts through the literal embedded center. -/
theorem centralizer_inner_image (B U : Subgroup G)
    (hU : U ≤ normalizer (B : Set G))
    (hc : Nat.Coprime (Nat.card U) (Nat.card (center B))) :
    ((B ⊓ centralizer (U : Set G)).subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom =
      (B.subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom ⊓
        centralizer ((U.subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom : Set (MulAut B)) := by
  let N := normalizer (B : Set G)
  let f := B.normalizerMonoidHom
  let Z := (center B).map B.subtype
  let C := ((B ⊓ centralizer (U : Set G)).subgroupOf N).map f
  have hZB : Z ≤ B := map_subtype_le _
  have hZsub : Z.subgroupOf B = center B := comap_map_eq_self_of_injective B.subtype_injective _
  have hZN : U ≤ normalizer (Z : Set G) :=
    hU.trans (normalizer_le_normalizer_characteristic_image B (center B))
  have hzero : Z.subgroupOf N ≤ f.ker := by
    rintro x ⟨b,hb,he⟩
    rw [normalizerMonoidHom_ker]
    intro k hk
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hb ⟨k,hk⟩)
  have hcentral : C ≤ centralizer ((U.subgroupOf N).map f : Set (MulAut B)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨u,hu,rfl⟩
    have he : u*x=x*u := Subtype.ext (hx.2 u.val hu)
    simpa only [map_mul] using congrArg f he
  apply le_antisymm (le_inf (map_mono (comap_mono inf_le_left)) hcentral)
  rintro a ⟨⟨x,hx,rfl⟩,ha⟩
  have hfixed (u : G) (hu : u ∈ U) : MulAut.conj u x.val / x.val ∈ Z := by
    let un : N := ⟨u,hU hu⟩
    let d : N := un*x*un⁻¹/x
    have hdB : d.val ∈ B := B.div_mem ((mem_normalizer_iff.mp (hU hu) x.val).mp hx) hx
    have hdker : d ∈ f.ker := by
      change f (un*x*un⁻¹/x) = 1
      have he := ha (f un) (mem_map_of_mem f hu)
      simp only [map_div,map_mul,map_inv]
      rw [he]
      simp only [mul_assoc, mul_inv_cancel, mul_one, div_self']
    rw [normalizerMonoidHom_ker] at hdker
    refine ⟨⟨d.val,hdB⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (hdker b.val b.property)
  let : (Z.subgroupOf B).Normal := hZsub.symm ▸ inferInstance
  let : IsMulCommutative (Z.subgroupOf B) := hZsub.symm ▸ inferInstance
  have hxjoin := mem_centralizer_sup_of_coprime_fixed_coset B Z U hZB hU hZN
    (by rw [card_map_of_injective B.subtype_injective]; exact hc) x.val hx hfixed
  have hjoin : (B ⊓ centralizer (U : Set G)) ⊔ Z ≤ (C.comap f).map N.subtype := by
    apply sup_le
    · intro b hb
      exact ⟨⟨b,B.le_normalizer hb.1⟩,mem_map_of_mem f hb,rfl⟩
    · intro b hb
      refine ⟨⟨b,B.le_normalizer (hZB hb)⟩,?_,rfl⟩
      change f ⟨b,B.le_normalizer (hZB hb)⟩ ∈ C
      rw [show f ⟨b,B.le_normalizer (hZB hb)⟩ = 1 from hzero hb]
      exact C.one_mem
  obtain ⟨y,hy,he⟩ := hjoin hxjoin
  have hey : y=x := Subtype.ext he
  change f y ∈ C at hy
  change f x ∈ C
  exact hey ▸ hy

/-- Centralizers in a component supplemented by fixed elements lift through
its normalizer action when the component center is coprime to the actor. -/
theorem centralizer_supplement_image (B U R : Subgroup G)
    (hU : U ≤ normalizer (B : Set G)) (hR : R ≤ normalizer (B : Set G))
    (hRC : R ≤ centralizer (U : Set G))
    (hc : Nat.Coprime (Nat.card U) (Nat.card (center B))) :
    (((B ⊔ R) ⊓ centralizer (U : Set G)).subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom =
      ((B ⊔ R).subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom ⊓
        centralizer ((U.subgroupOf (normalizer (B : Set G))).map B.normalizerMonoidHom : Set (MulAut B)) := by
  let N := normalizer (B : Set G)
  let f := B.normalizerMonoidHom
  let C := centralizer ((U.subgroupOf N).map f : Set (MulAut B))
  have hcentral {x : N} (hx : x.val ∈ centralizer (U : Set G)) : f x ∈ C := by
    rintro _ ⟨u,hu,rfl⟩
    have he : u*x=x*u := Subtype.ext (hx u.val hu)
    simpa only [map_mul] using congrArg f he
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨mem_map_of_mem f hx.1,hcentral hx.2⟩
  rintro _ ⟨⟨x,hx,rfl⟩,hxC⟩
  have hx' : x ∈ B.subgroupOf N ⊔ R.subgroupOf N := by
    rw [←subgroupOf_sup B.le_normalizer hR]
    exact hx
  let : (B.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨b,hb,r,hr,hbr⟩ := mem_sup_of_normal_left.mp hx'
  have hbC : f b ∈ C := by
    have hh := C.mul_mem hxC (C.inv_mem (hcentral (hRC hr)))
    rw [←hbr,map_mul] at hh
    simpa only [f, mul_inv_cancel_right] using hh
  have hb' : f b ∈ ((B ⊓ centralizer (U : Set G)).subgroupOf N).map f :=
    (centralizer_inner_image B U hU hc).symm ▸ ⟨mem_map_of_mem f hb,hbC⟩
  obtain ⟨d,hd,he⟩ := hb'
  refine ⟨d*r,⟨mul_mem_sup hd.1 hr,(centralizer (U : Set G)).mul_mem hd.2 (hRC hr)⟩,?_⟩
  rw [map_mul,he,←map_mul,hbr]

end Subgroup.NormalizerAction
