module

public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Elementary subgroups preserving a p-subgroup's normalizer

For a nontrivial finite p-subgroup U, the ambient image of Ω₁(Z(U)) is
nontrivial, elementary abelian, and contained in U. Every element normalizing
U normalizes this image. In particular, when U is normal inside a fixed
subgroup P, this elementary subgroup is normal inside P too.

This is the characteristic-center argument behind the elementary-normalizer
reduction for maximal two-local subgroups. Keeping the containment in U
allows its use before an ambient Sylow certificate or maximality is available.

Source: the center theorem for finite p-groups, Cauchy's theorem, and
characteristic-subgroup transitivity, as formalized in the imported modules.
-/

namespace Subgroup

/-- A nontrivial finite p-subgroup has a nontrivial elementary subgroup
whose ambient normalizer contains its own ambient normalizer. -/
public theorem exists_nontrivial_elementary_with_normalizer_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hU : IsPGroup p U) (hne : U ≠ ⊥) :
    ∃ E : Subgroup G, E ≠ ⊥ ∧ E ≤ U ∧ IsElementaryAbelian p E ∧
      normalizer (U : Set G) ≤ normalizer (E : Set G) := by
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hne
  let O := omega₁ (center U) (p := p)
  let : O.Characteristic := omega₁_characteristic _
  let C := O.map (center U).subtype
  let E := C.map U.subtype
  let : IsElementaryAbelian p O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian p C := IsElementaryAbelian.map _
  let : IsElementaryAbelian p E := IsElementaryAbelian.map _
  refine ⟨E, ?_, map_subtype_le C, inferInstance,
    normalizer_le_normalizer_characteristic_image U C⟩
  intro he
  apply omega_center_ne_bot hU
  exact map_injective U.subtype_injective (he.trans (map_bot U.subtype).symm)

end Subgroup
