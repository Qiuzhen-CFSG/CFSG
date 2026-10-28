module
public import Theory.GroupTheory.ElementaryEightPlanePoint

/-!
# Transport of an actual elementary-eight plane image

An injective homomorphism transports the invariant plane and its order-24
actor subgroup through the induced automorphism equivalence. Every transported
actor is still realized by conjugation in the new ambient group.

The Omega normalizer construction uses this to pass from its faithful local
section to the literal elementary eight in the original ambient group.
Source: Aschbacher--Smith 15.1.11, printed p.1089.
-/

public section
open Subgroup
namespace ElementaryEightPlaneImage

/-- Transport a plane-stabilizer image through an injective group homomorphism. -/
noncomputable def map
    {G H : Type*} [Group G] [Group H] {U:Subgroup G}
    (plane:ElementaryEightPlaneImage U) (i:G→*H) (hi:Function.Injective i) :
    ElementaryEightPlaneImage (U.map i) := by
  let e := U.equivMapOfInjective i hi
  let a := MulAut.congr e
  refine ⟨plane.W.map e.toMonoidHom,?_,plane.J.map a.toMonoidHom,?_,?_,?_⟩
  · rw [card_map_of_injective e.injective]
    exact plane.plane_card
  · rw [card_map_of_injective a.injective]
    exact plane.image_card
  · rintro _ ⟨j,hj,rfl⟩
    obtain ⟨n,rfl⟩ := plane.le_range hj
    let m:normalizer (U.map i:Set H) :=
      ⟨i n, U.le_normalizer_map i (mem_map_of_mem i n.property)⟩
    refine ⟨m,?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    change _ = e (U.normalizerMonoidHom n (e.symm (e x)))
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change i n * i x * (i n)⁻¹ = i ((n:G)*(x:G)*(n:G)⁻¹)
    simp only [map_mul,map_inv]
  · rintro ⟨_,j,hj,rfl⟩ y
    obtain ⟨x,rfl⟩ := e.surjective y
    change e (j (e.symm (e x)))∈plane.W.map e.toMonoidHom ↔ e x∈plane.W.map e.toMonoidHom
    rw [e.symm_apply_apply]
    simp only [mem_map_equiv,e.symm_apply_apply]
    exact plane.stable ⟨j,hj⟩ x
end ElementaryEightPlaneImage
