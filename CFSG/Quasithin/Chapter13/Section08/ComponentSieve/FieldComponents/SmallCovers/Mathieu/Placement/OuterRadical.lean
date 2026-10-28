module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.HexadLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.OuterRadical.Embedding
public import Theory.GroupTheory.PCoreImage
public import Theory.Mathieu.M22.Properties.OuterHexadRadical

/-!
# Transport of the hexad radical through the actual star quotient

The faithful design action is composed with H → H/O₂(H), retaining its
kernel O₂(H). The actual lift K₁ of an M₂₂ hexad stabilizer maps onto that
stabilizer. If T* stabilizes the hexad, the image of K₁T lies between the
inner and full design stabilizers. The p-group-kernel image theorem then
transports the native two-core calculation, including the possible outer
supplement, to the actual radical of K₁T.

The native calculation is discharged in `hexadRadical_image` and
`exists_hexadRadicalMap`. The parent chooses the hexad and proves the
T-stabilization condition and the required containment in L₁T; these
transport results do not assert the source placement. The restricted radical
map to M₂₂ retains its exact range, kernel, and component coordinates.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
namespace Setup
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : Setup H K L₁ T G₁ M)
include s

/-- The composite of the literal star quotient and its faithful design action. -/
noncomputable def starDesignMap : H →* m22DesignAut :=
  s.designHom.comp (QuotientGroup.mk' (pCore 2 H))

/-- The composite has precisely the original star kernel; faithfulness is proved upstream. -/
theorem starDesignMap_ker : s.starDesignMap.ker = pCore 2 H := by
  rw [starDesignMap, MonoidHom.ker_comp_of_injective _ _ s.designHom_injective,
    QuotientGroup.ker_mk']

/-- The design map agrees with the chosen intrinsic component coordinates. -/
theorem starDesignMap_component (k : K) :
    s.starDesignMap ⟨k, s.component_le k.property⟩ =
      M22ValueBound.Concrete.inclusion (componentMap K s.model k) := by
  rw [starDesignMap, MonoidHom.comp_apply,
    ← Components.componentStarEquiv_mk H K s.component_le s.component,
    s.designHom_component]
  rfl

/-- Subgroups of K have the same images in the two compatible coordinate systems. -/
theorem starDesignMap_image (X : Subgroup G) (hXK : X ≤ K) :
    (X.subgroupOf H).map s.starDesignMap =
      (markedImage K X s.model).map M22ValueBound.Concrete.inclusion := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K := ⟨x.val, hXK hx⟩
    refine ⟨componentMap K s.model k, ⟨k, hx, rfl⟩, ?_⟩
    exact (s.starDesignMap_component k).symm
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k.val, s.component_le k.property⟩, hk, s.starDesignMap_component k⟩

/-- The actual inverse-image lift maps onto the native hexad stabilizer. -/
theorem starDesignMap_hexadLift (B : Finset (Fin 22)) :
    ((hexadLift K s.model B).subgroupOf H).map s.starDesignMap =
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion := by
  rw [s.starDesignMap_image _ (hexadLift_le K s.model B), hexadLift_image]

/-- The actual subgroup K₁T inside H, before taking its intrinsic two-core. -/
noncomputable def hexadOvergroup (B : Finset (Fin 22)) : Subgroup H :=
  (hexadLift K s.model B ⊔ T).subgroupOf H

/-- The image includes the entire inner stabilizer and the actual image of T. -/
theorem hexadOvergroup_image (B : Finset (Fin 22)) :
    (s.hexadOvergroup B).map s.starDesignMap =
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion ⊔
        (Source.starImage H T).map s.designHom := by
  rw [hexadOvergroup,
    subgroupOf_sup ((hexadLift_le K s.model B).trans s.component_le)
      (le_sup_right.trans s.seed_join_sylow_le), Subgroup.map_sup,
    s.starDesignMap_hexadLift, Source.starImage, map_map]
  rfl

/-- The explicit stabilization assumption gives the bounds for the native calculation. -/
theorem hexadOvergroup_image_bounds (B : Finset (Fin 22))
    (hT : (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B) :
    (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion ≤
        (s.hexadOvergroup B).map s.starDesignMap ∧
      (s.hexadOvergroup B).map s.starDesignMap ≤ MulAction.stabilizer m22DesignAut B := by
  rw [s.hexadOvergroup_image]
  refine ⟨le_sup_left, sup_le ?_ hT⟩
  rintro g ⟨x, hx, rfl⟩
  exact hx

/-- Conditional transport of a native radical calculation through the proved two-group kernel. -/
theorem hexadRadical_image_of_native {B : Finset (Fin 22)}
    (hT : (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B)
    (hnative : ∀ R : Subgroup m22DesignAut,
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion ≤ R →
      R ≤ MulAction.stabilizer m22DesignAut B →
      R.pCoreIn 2 = (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion) :
    ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion := by
  have hk : IsPGroup 2 s.starDesignMap.ker := by
    rw [s.starDesignMap_ker]
    exact pCore_isPGroup
  rw [map_pCoreIn_of_ker_isPGroup s.starDesignMap hk]
  exact hnative _ (s.hexadOvergroup_image_bounds B hT).1
    (s.hexadOvergroup_image_bounds B hT).2

/-- The actual radical has the native pointwise-kernel image, even with an outer supplement. -/
theorem hexadRadical_image {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hT : (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B) :
    ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion :=
  s.hexadRadical_image_of_native hT (M22OuterHexad.radical_eq hB)

/-- Restrict the composite on the actual radical, using its proved image to land in M₂₂. -/
noncomputable def hexadRadicalMapOfImage (B : Finset (Fin 22))
    (hi : ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion) :
    (s.hexadOvergroup B).pCoreIn 2 →* M22 :=
  (subgroupOfEquivOfLe M22_le_hexadDesignAut).toMonoidHom.comp
    ((s.starDesignMap.comp ((s.hexadOvergroup B).pCoreIn 2).subtype).codRestrict
      M22ValueBound.Concrete.inner (by
        intro x
        have hx : s.starDesignMap x.val ∈
            (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion :=
          hi ▸ mem_map_of_mem s.starDesignMap x.property
        exact M22ValueBound.Concrete.inclusion_range ▸ map_le_range _ _ hx))

/-- The restricted map retains the ambient design value on every radical element. -/
theorem hexadRadicalMapOfImage_compatibility (B : Finset (Fin 22))
    (hi : ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion)
    (x : (s.hexadOvergroup B).pCoreIn 2) :
    M22ValueBound.Concrete.inclusion (s.hexadRadicalMapOfImage B hi x) =
      s.starDesignMap x.val := rfl

/-- The range is the native pointwise kernel, by injectivity of its design inclusion. -/
theorem hexadRadicalMapOfImage_range (B : Finset (Fin 22))
    (hi : ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion) :
    (s.hexadRadicalMapOfImage B hi).range = m22HexadPointwiseKernel B := by
  apply Subgroup.map_injective M22ValueBound.Concrete.inclusion_injective
  rw [← MonoidHom.range_comp]
  have he : M22ValueBound.Concrete.inclusion.comp (s.hexadRadicalMapOfImage B hi) =
      s.starDesignMap.comp ((s.hexadOvergroup B).pCoreIn 2).subtype := by
    apply MonoidHom.ext
    intro x
    exact s.hexadRadicalMapOfImage_compatibility B hi x
  rw [he, MonoidHom.range_comp, range_subtype]
  exact hi


/-- The restricted kernel is exactly the intersection with O₂(H). -/
theorem hexadRadicalMapOfImage_ker (B : Finset (Fin 22))
    (hi : ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion) :
    (s.hexadRadicalMapOfImage B hi).ker =
      (pCore 2 H).subgroupOf ((s.hexadOvergroup B).pCoreIn 2) := by
  ext x
  change s.hexadRadicalMapOfImage B hi x = 1 ↔ x.val ∈ pCore 2 H
  rw [← s.starDesignMap_ker]
  change s.hexadRadicalMapOfImage B hi x = 1 ↔ s.starDesignMap x.val = 1
  rw [← s.hexadRadicalMapOfImage_compatibility B hi x,
    ← M22ValueBound.Concrete.inclusion.map_one]
  exact M22ValueBound.Concrete.inclusion_injective.eq_iff.symm

/-- On elements of K, the radical map agrees with the supplied component model. -/
theorem hexadRadicalMapOfImage_component (B : Finset (Fin 22))
    (hi : ((s.hexadOvergroup B).pCoreIn 2).map s.starDesignMap =
      (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion)
    (x : (s.hexadOvergroup B).pCoreIn 2) (k : K) (hxk : x.val.val = k.val) :
    s.hexadRadicalMapOfImage B hi x = componentMap K s.model k := by
  apply M22ValueBound.Concrete.inclusion_injective
  rw [s.hexadRadicalMapOfImage_compatibility]
  have he : x.val = (⟨k, s.component_le k.property⟩ : H) := Subtype.ext hxk
  rw [he, s.starDesignMap_component]

/-- Conditional construction of the actual radical map with range, kernel and coordinate compatibility. -/
theorem exists_hexadRadicalMap_of_native {B : Finset (Fin 22)}
    (hT : (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B)
    (hnative : ∀ R : Subgroup m22DesignAut,
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion ≤ R →
      R ≤ MulAction.stabilizer m22DesignAut B →
      R.pCoreIn 2 = (m22HexadPointwiseKernel B).map M22ValueBound.Concrete.inclusion) :
    ∃ f : (s.hexadOvergroup B).pCoreIn 2 →* M22,
      f.range = m22HexadPointwiseKernel B ∧
      f.ker = (pCore 2 H).subgroupOf ((s.hexadOvergroup B).pCoreIn 2) ∧
      (∀ x, M22ValueBound.Concrete.inclusion (f x) = s.starDesignMap x.val) ∧
      ∀ (x : (s.hexadOvergroup B).pCoreIn 2) (k : K),
        x.val.val = k.val → f x = componentMap K s.model k := by
  let hi := s.hexadRadical_image_of_native hT hnative
  exact ⟨s.hexadRadicalMapOfImage B hi, s.hexadRadicalMapOfImage_range B hi,
    s.hexadRadicalMapOfImage_ker B hi, s.hexadRadicalMapOfImage_compatibility B hi, s.hexadRadicalMapOfImage_component B hi⟩

/-- The actual radical map with its exact range, kernel, and component coordinates.
Only the chosen hexad and stabilization by T* remain source placement inputs. -/
theorem exists_hexadRadicalMap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hT : (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B) :
    ∃ f : (s.hexadOvergroup B).pCoreIn 2 →* M22,
      f.range = m22HexadPointwiseKernel B ∧
      f.ker = (pCore 2 H).subgroupOf ((s.hexadOvergroup B).pCoreIn 2) ∧
      (∀ x, M22ValueBound.Concrete.inclusion (f x) = s.starDesignMap x.val) ∧
      ∀ (x : (s.hexadOvergroup B).pCoreIn 2) (k : K),
        x.val.val = k.val → f x = componentMap K s.model k :=
  s.exists_hexadRadicalMap_of_native hT (M22OuterHexad.radical_eq hB)

end Setup
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
