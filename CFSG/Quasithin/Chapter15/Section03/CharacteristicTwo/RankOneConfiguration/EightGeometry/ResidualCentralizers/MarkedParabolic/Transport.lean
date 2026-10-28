module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Basic
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Transport from the component quotient to its marked alternating image

Relative normality embeds the component two-core in the overgroup two-core.
The kernel of the marked component map is therefore exactly O₂(L), yielding
an actual quotient equivalence with A₈. The image identity allows a geometric
parabolic in A₈ to be pulled back to the original component.

Source: Aschbacher–Smith, 15.3.32(4), printed pp.1132–1133.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G : Type*} [Group G]

private theorem component_core_le_overgroup_core (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal) :
    c.L.pCoreIn 2 ≤ I.pCoreIn 2 := by
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
    ((pCoreIn_le 2 c.L).trans (component_le c))
    (hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))

/-- The component two-core lies in the fixed-plane centralizer. -/
theorem component_core_le_fixedPlane_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    c.L.pCoreIn 2 ≤ c.L ⊓ centralizer (d.ZS : Set G) := by
  refine le_inf (pCoreIn_le 2 c.L) ?_
  exact (component_core_le_overgroup_core d c hn).trans
    ((hP ▸ pCoreIn_le_sylow I P).trans (sylow_le_fixedPlane_centralizer d))

/-- The marked component map has precisely the intrinsic component two-core as kernel. -/
theorem componentMap_kernel_of_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (NaturalModule.componentMap d c e hmark).ker = pCore 2 c.L := by
  have hk : (NaturalModule.componentMap d c e hmark).ker =
      ((d.starMap I).ker).comap (inclusion (component_le c)) := by
    ext l
    change (⟨e (d.starMap I (inclusion (component_le c) l)), _⟩ : alternatingGroup (Fin 8)) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact e.map_eq_one_iff
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [hk]
    exact (star_kernel_isTwo d c P hP hC).comap_of_injective _
      (inclusion_injective (component_le c))
  · rw [hk]
    intro l hl
    have hmem := core_le_star_kernel d P hP
      (component_core_le_overgroup_core d c hn (mem_map_of_mem _ hl))
    obtain ⟨i, hi, he⟩ := hmem
    change inclusion (component_le c) l ∈ (d.starMap I).ker
    exact (Subtype.ext he : i = inclusion (component_le c) l) ▸ hi

/-- The component quotient is actually isomorphic to the marked alternating group. -/
noncomputable def componentQuotientEquiv (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq
    (componentMap_kernel_of_centralizer d c hn P hP hC e hmark).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (NaturalModule.componentMap d c e hmark)
      (NaturalModule.componentMap_surjective d c e hmark))

/-- The quotient equivalence preserves the original marked component map. -/
@[simp] theorem componentQuotientEquiv_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) (l : c.L) :
    componentQuotientEquiv d c hn P hP hC e hmark (QuotientGroup.mk' (pCore 2 c.L) l) =
      NaturalModule.componentMap d c e hmark l := rfl

/-- Ambient star images agree with images under the component quotient map. -/
theorem componentMap_image (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (K : Subgroup G) (hKL : K ≤ c.L) :
    ((K.subgroupOf c.L).map (NaturalModule.componentMap d c e hmark)).map
        (alternatingGroup (Fin 8)).subtype = (d.starImage I K).map e.toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨d.starMap I (inclusion (component_le c) l),
      ⟨inclusion (component_le c) l, hl, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨NaturalModule.componentMap d c e hmark ⟨i, hKL hi⟩,
      ⟨⟨i, hKL hi⟩, hi, rfl⟩, rfl⟩

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

/-- Marked image equality pulls back exactly when the component core is contained. -/
theorem componentMap_preimage (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hK : (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map e.toMonoidHom =
      fourStabilizer ⊓ alternatingGroup (Fin 8)) :
    (fourStabilizer.subgroupOf (alternatingGroup (Fin 8))).comap
      (NaturalModule.componentMap d c e hmark) =
        (c.L ⊓ centralizer (d.ZS : Set G)).subgroupOf c.L := by
  let K := c.L ⊓ centralizer (d.ZS : Set G)
  have him : (K.subgroupOf c.L).map (NaturalModule.componentMap d c e hmark) =
      fourStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
    apply map_injective (alternatingGroup (Fin 8)).subtype_injective
    rw [componentMap_image d c e hmark K inf_le_left,
      subgroupOf_map_subtype, hK]
  rw [← him, comap_map_eq_self]
  rw [componentMap_kernel_of_centralizer d c hn P hP hC e hmark]
  intro l hl
  exact component_core_le_fixedPlane_centralizer d c hn P hP (mem_map_of_mem _ hl)

/-- Maximality of the concrete even four-block subgroup lifts through the two-core. -/
theorem centralizer_isCoatom_of_marked_image (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hK : (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map e.toMonoidHom =
      fourStabilizer ⊓ alternatingGroup (Fin 8))
    (hmax : IsCoatom (fourStabilizer.subgroupOf (alternatingGroup (Fin 8)))) :
    IsCoatom ((c.L ⊓ centralizer (d.ZS : Set G)).subgroupOf c.L) := by
  rw [← componentMap_preimage d c hn P hP hC e hmark hK]
  exact isCoatom_comap_of_surjective (NaturalModule.componentMap_surjective d c e hmark) hmax

/-- Pull back the actual binary two-plane parabolic to the component quotient. -/
noncomputable def endNodeModelOfMarkedImage (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hK : (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map e.toMonoidHom =
      fourStabilizer ⊓ alternatingGroup (Fin 8))
    (j : alternatingGroup (Fin 8) ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (hd : Module.finrank (ZMod 2) W = 2)
    (hj : (BinaryLinear.parabolic W).comap j.toMonoidHom =
      fourStabilizer.subgroupOf (alternatingGroup (Fin 8))) :
    EndNodeParabolicModel c.L (c.L ⊓ centralizer (d.ZS : Set G)) where
  le_component := inf_le_left
  quotient := (componentQuotientEquiv d c hn P hP hC e hmark).trans j
  plane := W
  dimension := hd
  preimage := by
    change ((BinaryLinear.parabolic W).comap j.toMonoidHom).comap
      (NaturalModule.componentMap d c e hmark) = _
    rw [hj]
    exact componentMap_preimage d c hn P hP hC e hmark hK

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
end
