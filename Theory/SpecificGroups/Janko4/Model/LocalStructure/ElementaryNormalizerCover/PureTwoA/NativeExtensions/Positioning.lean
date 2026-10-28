module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.Images

/-!
# Two native image positions for marked elementary extensions

Three of the four elementary image containers are conjugate by certified
permutations in the pair-centralizer image. Lifting those permutations through
the original projection conjugates any elementary extension into one of two
literal image positions. The lift centralizes the native pair pointwise.
The same ambient conjugator transports the whole centralizer and normalizer.

This is a native image reduction for the nontrivial-image step of
Kleidman--Wilson (1988), Section 2.1, p.489. It does not replace the further
pure-lift, extraspecial-container or exceptional-centralizer arguments.
-/

set_option Elab.async false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality QuotientCount.Image
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true

private def transportIndex : Fin 4 → Fin 96 := ![0,0,2,3]
private def targetBlock (r : Fin 4) : Fin 4 := if r = 0 then 0 else 1

private theorem conjugate_generator (r j : Fin 4) : ∃ i : Fin 16,
    (MulAut.conj (element (transportIndex r))) (element (blockBasis r j)) =
      element (blockIndex (targetBlock r) i) := by
  have hh : ∀ r j : Fin 4, ∃ i : Fin 16,
      ((MulAut.conj (element (transportIndex r))) (element (blockBasis r j))).val =
        (element (blockIndex (targetBlock r) i)).val := by decide +kernel
  obtain ⟨i,hi⟩ := hh r j
  exact ⟨i,Subtype.ext hi⟩

private theorem block_normalization (r : Fin 4) :
    (imageBlock r).map (MulAut.conj (element (transportIndex r))).toMonoidHom =
      imageBlock (targetBlock r) := by
  have hle : (imageBlock r).map (MulAut.conj (element (transportIndex r))).toMonoidHom ≤
      imageBlock (targetBlock r) := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change (MulAut.conj (element (transportIndex r))) (element (blockBasis r j)) ∈ imageBlock (targetBlock r)
    obtain ⟨i,hi⟩ := conjugate_generator r j
    exact (mem_imageBlock_iff _ _).mpr ⟨i,hi.symm⟩
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (MulAut.conj (element (transportIndex r))).injective,
    imageBlock_card,imageBlock_card]

private theorem local_image_conjugate (X : Subgroup Model) (hXM : X ≤ M) (g : M) :
    ((X.map (MulAut.conj (g : Model)).toMonoidHom).subgroupOf M).map starHom =
      ((X.subgroupOf M).map starHom).map (MulAut.conj (starHom g)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hxy⟩ := hy
    let x0 : M := ⟨x,hXM hx⟩
    refine ⟨starHom x0,mem_map_of_mem starHom (show x0 ∈ X.subgroupOf M from hx),?_⟩
    have he : (MulAut.conj g) x0 = y := Subtype.ext hxy
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  · rintro _ ⟨q,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨(MulAut.conj g) x,?_,?_⟩
    · exact mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom hx
    · simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- An actual pair-centralizing ambient conjugator reduces the elementary
extension to two literal Mathieu-image positions, with full local transport. -/
theorem extension_two_image_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) :
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ Y ≤ M ∧ centralizer (Y : Set Model) ≤ M ∧
      ((Y.subgroupOf M).map starHom ≤ imageBlock 0 ∨
        (Y.subgroupOf M).map starHom ≤ imageBlock 1) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  obtain ⟨r,hr⟩ := extension_image_cover X hpair
  obtain ⟨g,hg,hproj⟩ := (mem_pair_image_iff _).mpr ⟨transportIndex r,rfl⟩
  let Y := X.map (MulAut.conj (g : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hgc : (g : Model) ∈ centralizer (nativePair : Set Model) := by
    rw [centralizer_eq_local_map]
    exact mem_map_of_mem M.subtype hg
  have hPY : nativePair ≤ Y := by
    intro x hx
    have he : (MulAut.conj (g : Model)) x = x := by
      change (g : Model) * x * (g : Model)⁻¹ = x
      rw [← hgc x hx,mul_inv_cancel_right]
    exact he ▸ mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom (hpair hx)
  have hYM := elementary_overgroup_placement Y hPY
  have himage : (Y.subgroupOf M).map starHom ≤ imageBlock (targetBlock r) := by
    have ht := map_mono (f := (MulAut.conj (element (transportIndex r))).toMonoidHom) hr
    rw [block_normalization] at ht
    change ((X.map (MulAut.conj (g : Model)).toMonoidHom).subgroupOf M).map starHom ≤ _
    rw [local_image_conjugate X (elementary_overgroup_placement X hpair).1 g,hproj]
    exact ht
  refine ⟨⟨g,hg⟩,hPY,hYM.1,hYM.2,?_,?_,?_⟩
  · by_cases h0 : r = 0
    · exact Or.inl (by simpa only [targetBlock,h0,ite_true] using himage)
    · exact Or.inr (by simpa only [targetBlock,h0,ite_false] using himage)
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g : Model))).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g : Model))).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
