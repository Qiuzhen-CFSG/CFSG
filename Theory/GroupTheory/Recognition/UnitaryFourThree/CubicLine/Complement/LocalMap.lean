module
public import Theory.GroupTheory.SubgroupTransport
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.LocalRigidity

/-!
# Ambient transport for the original marked local normalizers

The original rigidity theorem supplies a marked normalizer isomorphism.
Composing it with the target subtype transports the actual ambient subgroups.
Centralization of D recovers W; intersection recovers the selected cubic
K∩V. The same map preserves normalizer membership, the displacement subgroup
[V,z], and the literal existential K-conjugate displacement test.
These are the local inputs used by the comparison of cubic geometries.

Source: Aschbacher, *Sporadic Groups* (1994),45.11,pp248–249.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
open Theory.GroupTheory.SubgroupTransport
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} {h : IsType z} {h' : IsType z'}
  {P : Sylow 3 (centralizer z)} {P' : Sylow 3 (centralizer z')}
  (c : SourceConfiguration h P) (c' : SourceConfiguration h' P')

structure LocalMap where
  equiv : normalizer (c.W : Set G) ≃* normalizer (c'.W : Set G')
  map_odd : (c.D.subgroupOf (normalizer (c.W : Set G))).map equiv.toMonoidHom=
    c'.D.subgroupOf (normalizer (c'.W : Set G'))
  map_complement : (c.K.subgroupOf (normalizer (c.W : Set G))).map equiv.toMonoidHom=
    c'.K.subgroupOf (normalizer (c'.W : Set G'))
  map_kernel : (c.V.subgroupOf (normalizer (c.W : Set G))).map equiv.toMonoidHom=
    c'.V.subgroupOf (normalizer (c'.W : Set G'))
  map_involution : ∀ hz hz', equiv ⟨z,hz⟩=⟨z',hz'⟩

/-- The original local rigidity supplies this transport package without extra premises. -/
theorem exists_localMap : Nonempty (LocalMap c c') := by
  obtain ⟨e,hD,hK,hV,hz⟩ := c.exists_local_normalizer_equiv c'
  exact ⟨⟨e,hD,hK,hV,hz⟩⟩

omit [Finite G] [Finite G'] in
private theorem local_odd_le : c.D≤normalizer (c.W : Set G) := le_sup_left.trans_eq c.complement_product.symm
omit [Finite G] [Finite G'] in
private theorem local_kernel_le : c.V≤normalizer (c.W : Set G) := by
  have hWX : c.W≤c.X := zpowers_le.mpr (c.actors_eq.le c.actors.x.property)
  exact ((map_subtype_le _).trans (centralizer_le hWX)).trans (centralizer_le_normalizer _)
omit [Finite G] [Finite G'] in
private theorem local_line_le : c.W≤normalizer (c.W : Set G) := c.W.le_normalizer
omit [Finite G] [Finite G'] in
private theorem local_involution_mem : z∈normalizer (c.W : Set G) :=
  (c.complement_le c.involution_mem_complement).2

namespace LocalMap
variable {c c'} (L : LocalMap c c')
omit [Finite G] [Finite G']

@[expose] def ambient : normalizer (c.W : Set G) →* G' := ambientHom L.equiv
@[expose] def map (H : Subgroup G) : Subgroup G' := image L.equiv H

theorem ambient_injective : Function.Injective L.ambient :=
  ambientHom_injective L.equiv

theorem ambient_ne_one_iff (n : normalizer (c.W : Set G)) : L.ambient n≠1 ↔ (n:G)≠1 := by
  rw [ne_eq,ne_eq,←L.ambient.map_one]
  exact not_congr ((L.ambient_injective.eq_iff).trans Subtype.ext_iff)

theorem mem_map_iff (H : Subgroup G) (n : normalizer (c.W : Set G)) :
    L.ambient n∈L.map H ↔ (n:G)∈H := SubgroupTransport.mem_image_iff L.equiv H n

theorem odd_map : L.map c.D=c'.D :=
  image_eq_of_internal_eq L.equiv c'.local_odd_le L.map_odd

theorem complement_map : L.map c.K=c'.K :=
  image_eq_of_internal_eq L.equiv (c'.complement_le.trans inf_le_right) L.map_complement

theorem kernel_map : L.map c.V=c'.V :=
  image_eq_of_internal_eq L.equiv c'.local_kernel_le L.map_kernel

theorem odd_mem_iff (n : normalizer (c.W : Set G)) : L.ambient n∈c'.D ↔ (n:G)∈c.D := by
  rw [←L.odd_map]
  exact L.mem_map_iff c.D n

theorem complement_mem_iff (n : normalizer (c.W : Set G)) : L.ambient n∈c'.K ↔ (n:G)∈c.K := by
  rw [←L.complement_map]
  exact L.mem_map_iff c.K n

theorem kernel_mem_iff (n : normalizer (c.W : Set G)) : L.ambient n∈c'.V ↔ (n:G)∈c.V := by
  rw [←L.kernel_map]
  exact L.mem_map_iff c.V n

theorem axis_map : L.map (c.K⊓c.V)=c'.K⊓c'.V := by
  rw [map,image_inf]
  exact congrArg₂ (·⊓·) L.complement_map L.kernel_map

theorem line_map : L.map c.W=c'.W := by
  ext w
  constructor
  · rintro ⟨n,hn,rfl⟩
    have hc := (centralizes_iff L.equiv c.D c.local_odd_le n).mp (c.odd_centralizer.ge hn)
    change ((L.equiv n):G')∈Subgroup.centralizer (L.map c.D:Set G') at hc
    rw [L.odd_map] at hc
    exact c'.odd_centralizer.le hc
  · intro hw
    let n' : normalizer (c'.W : Set G') := ⟨w,c'.local_line_le hw⟩
    let n := L.equiv.symm n'
    have hnp : L.equiv n=n' := L.equiv.apply_symm_apply n'
    have hc : ((L.equiv n):G')∈Subgroup.centralizer (image L.equiv c.D:Set G') := by
      change ((L.equiv n):G')∈Subgroup.centralizer (L.map c.D:Set G')
      rw [L.odd_map,c'.odd_centralizer,hnp]
      exact hw
    have hn := (centralizes_iff L.equiv c.D c.local_odd_le n).mpr hc
    refine ⟨n,c.odd_centralizer.le hn,?_⟩
    exact congrArg Subtype.val hnp

theorem normalizes_kernel_iff (n : normalizer (c.W : Set G)) :
    (n:G)∈normalizer (c.V:Set G) ↔ L.ambient n∈normalizer (c'.V:Set G') := by
  have hh := normalizes_iff L.equiv c.V c.local_kernel_le n
  change _ ↔ L.ambient n∈normalizer (L.map c.V:Set G') at hh
  rwa [L.kernel_map] at hh

theorem normalizes_axis_iff (n : normalizer (c.W : Set G)) :
    (n:G)∈normalizer (c.K⊓c.V : Subgroup G) ↔
      L.ambient n∈normalizer (c'.K⊓c'.V : Subgroup G') := by
  have hh := normalizes_iff L.equiv (c.K⊓c.V) ((inf_le_left).trans (c.complement_le.trans inf_le_right)) n
  change _ ↔ L.ambient n∈normalizer (L.map (c.K⊓c.V):Set G') at hh
  rwa [L.axis_map] at hh

theorem involution_powers_map : L.map (zpowers z)=zpowers z' := by
  have hh := image_zpowers L.equiv (⟨z,c.local_involution_mem⟩:normalizer (c.W:Set G))
  rw [L.map_involution _ c'.local_involution_mem] at hh
  exact hh

theorem displacement_map : L.map ⁅c.V,zpowers z⁆=⁅c'.V,zpowers z'⁆ := by
  rw [map,image_commutator _ _ _ c.local_kernel_le (zpowers_le.mpr c.local_involution_mem)]
  exact congrArg₂ (fun H K => ⁅H,K⁆) L.kernel_map L.involution_powers_map

theorem displacement_mem_iff (n : normalizer (c.W : Set G)) :
    (n:G)∈⁅c.V,zpowers z⁆ ↔ L.ambient n∈⁅c'.V,zpowers z'⁆ := by
  rw [←L.displacement_map]
  exact (L.mem_map_iff _ n).symm

theorem exists_complement_conjugate_displacement_iff (n : normalizer (c.W : Set G)) :
    (∃ k∈c.K,k⁻¹*(n:G)*k∈⁅c.V,zpowers z⁆) ↔
      (∃ k'∈c'.K,k'⁻¹*L.ambient n*k'∈⁅c'.V,zpowers z'⁆) := by
  have hh := exists_conjugate_mem_iff L.equiv ⁅c.V,zpowers z⁆ c.K
    (c.complement_le.trans inf_le_right) n
  change _ ↔ ∃ k'∈L.map c.K,k'⁻¹*L.ambient n*k'∈L.map ⁅c.V,zpowers z⁆ at hh
  rwa [L.complement_map,L.displacement_map] at hh
end LocalMap
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
