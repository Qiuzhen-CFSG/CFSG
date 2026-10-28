module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneInvariant
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.SylowKernelCore

/-!
# Embedded elementary64 plane parabolics

All conclusions concern the original ambient subgroup. In particular the
normalizer, two-core, center and invariant subgroups use the same embedding.
-/

namespace Matrix.PSL3Four.FullPlaneNormalizer
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

public theorem embedded_plane
    (B W : Subgroup G) [Group.IsPerfect B] [IsElementaryAbelian 2 W]
    (f : B →* PSL) (hf : Function.Surjective f) (hk : f.ker=center B)
    (hkc : Nat.card f.ker=4) (hWB : W≤B) (hZW : centerIn B≤W)
    (hWc : Nat.card W=64) :
    let L := (normalizer (W.subgroupOf B : Set B)).map B.subtype
    Group.IsPerfect L ∧ Nat.card L=3840 ∧ L.pCoreIn 2=W ∧ ⁅W,L⁆=W ∧
      centerIn L=centerIn B ∧ L≤normalizer (W : Set G) ∧
      (∀ A : Subgroup G, A≤W → L≤normalizer (A : Set G) → A≤centerIn B ∨ A=W) := by
  let Q := W.subgroupOf B
  let N := normalizer (Q : Set B)
  let L := N.map B.subtype
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hWB
  have hQc : Nat.card Q=64 := (Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv).trans hWc
  have hkQ : f.ker≤Q := by
    rw [hk]
    intro x hx
    exact hZW (by rw [centerIn_eq_map_center]; exact ⟨x,hx,rfl⟩)
  have hc : f.ker≤center B := hk.le
  obtain ⟨hNp,hNc,hNz⟩ := full_plane_normalizer f hf hc Q hkQ (by rw [hkc,hQc])
  let := hNp
  have hperfect : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (N.equivMapOfInjective B.subtype B.subtype_injective).toMonoidHom)
    (N.equivMapOfInjective B.subtype B.subtype_injective).surjective
  obtain ⟨hcore,hcomm⟩ := full_plane_core f hf hc hkc Q hkQ hQc
  have hcore' : L.pCoreIn 2=W := by
    rw [←map_pCoreIn_of_injective 2 N B.subtype B.subtype_injective,hcore]
    exact map_subgroupOf_eq_of_le hWB
  have hcomm' : ⁅W,L⁆=W := by
    have hh := congrArg (Subgroup.map B.subtype) hcomm
    simpa only [Q,Subgroup.map_commutator,map_subgroupOf_eq_of_le hWB] using hh
  have hcenter : centerIn L=centerIn B := by
    rw [centerIn_eq_map_center,←N.map_embeddedCenter B.subtype B.subtype_injective,
      hNz,hk,←centerIn_eq_map_center]
  have hnormal : L≤normalizer (W : Set G) := by
    have hh := Q.le_normalizer_map B.subtype
    rwa [map_subgroupOf_eq_of_le hWB] at hh
  refine ⟨hperfect,(card_map_of_injective B.subtype_injective).trans (by simpa only [hkc] using hNc),
    hcore',hcomm',hcenter,hnormal,?_⟩
  intro A hAW hLA
  have hAB : A≤B := hAW.trans hWB
  have hnA : N≤normalizer (A.subgroupOf B : Set B) := by
    rw [←subgroupOf_normalizer_eq hAB]
    intro x hx
    exact hLA (mem_map_of_mem B.subtype hx)
  rcases full_plane_invariant f hf hc hkc Q hkQ hQc (A.subgroupOf B)
      (subgroupOf_mono B hAW) hnA with hz | he
  · left
    intro x hx
    rw [centerIn_eq_map_center]
    exact ⟨⟨x,hAB hx⟩,hk ▸ hz hx,rfl⟩
  · right
    have hh := congrArg (Subgroup.map B.subtype) he
    simpa only [Q,map_subgroupOf_eq_of_le hAB,map_subgroupOf_eq_of_le hWB] using hh

end Matrix.PSL3Four.FullPlaneNormalizer
