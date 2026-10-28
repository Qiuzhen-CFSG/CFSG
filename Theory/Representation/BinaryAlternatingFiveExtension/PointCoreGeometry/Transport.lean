module
public import Theory.Representation.BinaryAlternatingFiveExtension.PointCoreGeometry
/-!
# Literal transport of the point-core identities

An injective map preserves both centralizer tests, expressed inside the
image of the order-64 core. The modulo statement is elementwise, so no
normality of its central line in a larger ambient group is required.
For an actual subgroup marked by the Borel model, the core and residual
images are identified canonically. A marking of the vector subgroup also
identifies its commutator with the residual as its intersection with the
residual two-core.

Source: Aschbacher–Smith, proof of 14.6.9(i,l), printed p.1027.
-/
public section
namespace BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem mapped_geometry (f : BorelModel →* G) (hf : Function.Injective f) :
    let C := outerCore.map f
    let N := coreModel.map f
    let Z := fixedLine.map f
    C ⊓ centralizer (N : Set G) = Z ∧
      (∀ x ∈ C, (∀ a ∈ N, ⁅a,x⁆ ∈ Z) → x ∈ N) ∧
      ⁅C,(pResidual 2 BorelModel).map f⁆ = N ∧
      ⁅vectors.map f,(pResidual 2 BorelModel).map f⁆ = threeSpace.map f ∧
      (center N).map N.subtype = Z := by
  dsimp only
  have hcent : outerCore.map f ⊓ centralizer (coreModel.map f : Set G) = fixedLine.map f := by
    apply le_antisymm
    · rintro x ⟨⟨y,hy,rfl⟩,hc⟩
      apply mem_map_of_mem
      rw [←outerCore_centralizer_coreModel]
      refine ⟨hy,fun a ha => ?_⟩
      exact hf (by simpa only [map_mul] using hc (f a) (mem_map_of_mem f ha))
    · rintro x ⟨y,hy,rfl⟩
      refine ⟨mem_map_of_mem f ((fixedLine_le_coreModel.trans coreModel_le_outerCore) hy),?_⟩
      rintro a ⟨b,hb,rfl⟩
      simpa only [map_mul] using congrArg f (mem_center_iff.mp (fixedLine_le_center hy) b)
  refine ⟨hcent,?_,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩ hc
    apply mem_map_of_mem
    rw [←outerCore_centralizerModulo_coreModel]
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hy,fun a ha => ?_⟩
    apply (mem_map_iff_mem hf).mp
    rw [map_commutatorElement]
    exact hc (f a) (mem_map_of_mem f ha)
  · rw [←map_commutator,commutator_outerCore_residual]
  · rw [←map_commutator,commutator_vectors_residual]
  · apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      rw [←hcent]
      refine ⟨map_mono coreModel_le_outerCore y.property,?_⟩
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨a,ha⟩)
    · intro x hx
      have hN : x ∈ coreModel.map f := map_mono fixedLine_le_coreModel hx
      refine ⟨⟨x,hN⟩,?_,rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext ((hcent.symm ▸ hx).2 y y.property))

local instance : Finite BorelModel :=
  Finite.of_equiv (V × BinaryPermutation.AlternatingFiveBorel.B) SemidirectProduct.equivProd.symm

/-- Canonical two-core and residual-core geometry for any actual Borel marking. -/
theorem borel_ambient_geometry (H : Subgroup G) (e : H ≃* BorelModel) :
    let X := (pResidual 2 H).map H.subtype
    let N := X.pCoreIn 2
    let Z := (center N).map N.subtype
    H.pCoreIn 2 ⊓ centralizer (N : Set G) = Z ∧
      (∀ x ∈ H.pCoreIn 2, (∀ a ∈ N, ⁅a,x⁆ ∈ Z) → x ∈ N) ∧
      ⁅H.pCoreIn 2,X⁆ = N := by
  let f := H.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.symm.injective
  have hC : outerCore.map f = H.pCoreIn 2 := by
    rw [←pCore_eq_outerCore]
    change (pCore 2 BorelModel).map (H.subtype.comp e.symm.toMonoidHom) = _
    rw [←map_map,pCore_map_iso]
    rfl
  have hX : (pResidual 2 BorelModel).map f = (pResidual 2 H).map H.subtype := by
    change (pResidual 2 BorelModel).map (H.subtype.comp e.symm.toMonoidHom) = _
    rw [←map_map,map_pResidual_of_surjective 2 e.symm.toMonoidHom e.symm.surjective]
  have hN : coreModel.map f = ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
    rw [←residual_pCoreIn_eq_coreModel,map_pCoreIn_of_injective 2 _ f hf,hX]
  obtain ⟨hc,hm,hcomm,_,hz⟩ := mapped_geometry f hf
  dsimp only at hc hm hcomm hz ⊢
  rw [hC,hN] at hc hm
  rw [hC,hN,hX] at hcomm
  rw [hN] at hz
  rw [←hz] at hc hm
  exact ⟨hc,hm,hcomm⟩

/-- Retaining the marked vector subgroup identifies the literal moved space. -/
theorem marked_borel_vector_commutator (H : Subgroup G) (e : H ≃* BorelModel)
    (A : Subgroup G)
    (hA : A = vectors.map (H.subtype.comp e.symm.toMonoidHom)) :
    ⁅A,(pResidual 2 H).map H.subtype⁆ = A ⊓ ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
  let f := H.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.symm.injective
  have hX : (pResidual 2 BorelModel).map f = (pResidual 2 H).map H.subtype := by
    change (pResidual 2 BorelModel).map (H.subtype.comp e.symm.toMonoidHom) = _
    rw [←map_map,map_pResidual_of_surjective 2 e.symm.toMonoidHom e.symm.surjective]
  have hN : coreModel.map f = ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
    rw [←residual_pCoreIn_eq_coreModel,map_pCoreIn_of_injective 2 _ f hf,hX]
  rw [hA,←hN,←hX,←map_commutator,commutator_vectors_residual,←map_inf _ _ _ hf]
  congr 1
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1,hx.2,vectors_le_outerCore hx.1⟩
  · intro x hx
    exact ⟨hx.1,hx.2.1⟩
end BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry

namespace BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
open Subgroup
variable {G : Type*} [Group G]

/-- The marked intersection is the order-eight space used in the paired E₀. -/
theorem marked_borel_vector_intersection_card (H : Subgroup G) (e : H ≃* BorelModel)
    (A : Subgroup G)
    (hA : A = vectors.map (H.subtype.comp e.symm.toMonoidHom)) :
    Nat.card (A ⊓ ((pResidual 2 H).map H.subtype).pCoreIn 2 : Subgroup G) = 8 := by
  let f := H.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.symm.injective
  have hN : coreModel.map f = ((pResidual 2 H).map H.subtype).pCoreIn 2 := by
    rw [←residual_pCoreIn_eq_coreModel,map_pCoreIn_of_injective 2 _ f hf]
    change ((pResidual 2 BorelModel).map (H.subtype.comp e.symm.toMonoidHom)).pCoreIn 2 = _
    let : Finite BorelModel := Finite.of_equiv
      (V × BinaryPermutation.AlternatingFiveBorel.B) SemidirectProduct.equivProd.symm
    rw [←map_map,map_pResidual_of_surjective 2 e.symm.toMonoidHom e.symm.surjective]
  have hthree : vectors ⊓ coreModel = threeSpace := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1,hx.2.1⟩
    · intro x hx
      exact ⟨hx.1,hx.2,vectors_le_outerCore hx.1⟩
  rw [hA,←hN,←map_inf _ _ _ hf,hthree,threeSpace_eq_map,map_map]
  exact (card_map_of_injective (K := BinaryPermutation.AlternatingFiveFlag.three)
    (f := f.comp (SemidirectProduct.inl : V →* BorelModel))
    (hf.comp SemidirectProduct.inl_injective)).trans
    BinaryPermutation.AlternatingFiveFlag.three_card
end BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry
