module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceSylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SmallModels.SymmetricThree

/-!
# Returning from the temporary Thompson actor to original I₀

The Frattini comparison is applied to the quotient of original G_E by
C_{G_E}(V_E/E). It supplies representatives in the temporary Thompson
subgroup with identical section action. The paired first-summand kernel
then gives equality of their actual linear action images. This proves an
image comparison, not equality of Thompson subgroups in different groups.

The original action retains exactly its intersection with that section
kernel. Its moved space is unchanged. Pulling back the pointwise marker
stabilizer, once its source identification with I₀∩M is supplied, transfers
the index to the original ambient subgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.OriginalComparison
open Replacement BestReduction.FullCoreTransfer Replacement.Transvections
variable {G D W : Type*} [Group G] [Finite G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

noncomputable abbrev originalActor (T V E : Subgroup G) :=
  (lineI0 T V E).subgroupOf (temporaryLineNormalizer T V E)

omit [Finite G] [IsMulCommutative V] in
theorem originalActor_le_centralizer : originalActor T V E ≤ localCentralizer T V E := by
  intro x hx
  exact ⟨x.property, lineI_le_centralizer E hx.1⟩

omit [Finite G] [IsMulCommutative V] in
theorem temporary_maxJ_map :
    (elementaryAbelianMaxJ (localCentralizer T V E)).map (temporaryLineNormalizer T V E).subtype =
      elementaryAbelianMaxJ (temporaryCentralizer T V E) := by
  rw [← elementaryAbelianMaxJ_map_injective _ (temporaryLineNormalizer T V E).subtype_injective,
    map_subgroupOf_eq_of_le (show temporaryCentralizer T V E ≤ temporaryLineNormalizer T V E
      from inf_le_left)]

theorem original_image_eq (o : Geometry.OriginalData Y T V M E Pc)
    (s : temporaryLineNormalizer T V E →* D)
    (hk : (Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E) ⊓
      localCentralizer T V E ≤ s.ker) :
    (elementaryAbelianMaxJ (localCentralizer T V E)).map s =
      (originalActor T V E).map s := by
  let H := temporaryLineNormalizer T V E
  let C := localCentralizer T V E
  have hJI : elementaryAbelianMaxJ C ≤ originalActor T V E := by
    intro j hj
    apply temporaryMaxJ_le_lineI0 T V E o.line_le o.sylow o.sylow_image
    exact temporary_maxJ_map (T := T) (V := V) (E := E) ▸ mem_map_of_mem H.subtype hj
  apply le_antisymm (map_mono hJI)
  rintro _ ⟨x, hx, rfl⟩
  let L := lineNormalizer E
  let N := (Descent.sectionKernel V E).subgroupOf L
  let : N.Normal := Descent.sectionKernel_normal V E o.line_le
  let q := QuotientGroup.mk' N
  have heq := temporaryMaxJ_image_eq_lineI0 T V E o.line_le o.sylow o.sylow_image
    q (by rw [QuotientGroup.ker_mk'])
  let xL : L := ⟨x, x.property.1⟩
  have hmem : q xL ∈ ((elementaryAbelianMaxJ (temporaryCentralizer T V E)).subgroupOf L).map q := by
    rw [heq]
    exact mem_map_of_mem q hx
  obtain ⟨j, hj, hjx⟩ := hmem
  have hJC : elementaryAbelianMaxJ (temporaryCentralizer T V E) ≤ temporaryCentralizer T V E :=
    sSup_le fun _ hA => hA.1
  have hjC : (j : G) ∈ temporaryCentralizer T V E := hJC hj
  let jH : H := ⟨j, hjC.1⟩
  have hjJ : jH ∈ elementaryAbelianMaxJ C := by
    have hm : jH ∈ ((elementaryAbelianMaxJ C).map H.subtype).comap H.subtype := by
      change (j : G) ∈ (elementaryAbelianMaxJ C).map H.subtype
      rw [temporary_maxJ_map]
      exact hj
    rwa [comap_map_eq_self_of_injective H.subtype_injective] at hm
  have hN : j⁻¹ * xL ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (j⁻¹ * xL) = 1
    rw [map_mul, map_inv, hjx, inv_mul_cancel]
  have hkill : s (jH⁻¹ * x) = 1 :=
    hk ⟨hN, C.mul_mem (C.inv_mem ⟨jH.property, hjC.2⟩)
      (originalActor_le_centralizer hx)⟩
  have hs : s jH = s x := by
    rw [map_mul, map_inv, inv_mul_eq_one] at hkill
    exact hkill
  exact mem_map.mpr ⟨jH, hjJ, hs⟩

noncomputable def originalRepresentation
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W) :
    Representation (ZMod 2) (originalActor T V E) W :=
  σ.comp ((QuotientGroup.mk' (localCore T V E)).comp (originalActor T V E).subtype)

omit [Finite G] [IsMulCommutative V] in
theorem original_kernel
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) :
    (originalRepresentation σ).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (originalActor T V E) := by
  ext x
  let xC : localCentralizer T V E := ⟨x.val, originalActor_le_centralizer x.property⟩
  change xC ∈ (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
    (localCentralizer T V E).subtype)).ker ↔ _
  rw [hk]
  rfl

theorem original_actionImage (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) :
    actionImage (originalRepresentation σ) = actionImage (σ.comp (thompsonImage T V E).subtype) := by
  let H := temporaryLineNormalizer T V E
  let q := QuotientGroup.mk' (localCore T V E)
  let s := σ.asGroupHom.comp q
  have hs : (Descent.sectionKernel V E).subgroupOf H ⊓ localCentralizer T V E ≤ s.ker := by
    intro x hx
    have hx' : (⟨x, hx.2⟩ : localCentralizer T V E) ∈
        (σ.comp (q.comp (localCentralizer T V E).subtype)).ker := hk.symm ▸ hx.1
    exact Units.ext hx'
  have he := original_image_eq o s hs
  have h₀ : actionImage (originalRepresentation σ) = (originalActor T V E).map s := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h₁ : actionImage (σ.comp (thompsonImage T V E).subtype) =
      (elementaryAbelianMaxJ (localCentralizer T V E)).map s := by
    rw [show s = σ.asGroupHom.comp q from rfl, ← map_map]
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact h₀.trans (he.symm.trans h₁.symm)

noncomputable def actionSurjection (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) :
    originalActor T V E →* actionImage (σ.comp (thompsonImage T V E).subtype) :=
  (MulEquiv.subgroupCongr (original_actionImage o σ hk)).toMonoidHom.comp
    (actionHom (originalRepresentation σ))

theorem actionSurjection_surjective (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) : Function.Surjective (actionSurjection o σ hk) :=
  (MulEquiv.subgroupCongr (original_actionImage o σ hk)).surjective.comp
    (originalRepresentation σ).asGroupHom.rangeRestrict_surjective

theorem actionSurjection_apply (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) (g : originalActor T V E) :
    imageRepresentation (σ.comp (thompsonImage T V E).subtype) (actionSurjection o σ hk g) =
      originalRepresentation σ g := rfl

theorem original_moved_eq (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E)) :
    Coinvariants.ker (originalRepresentation σ) =
      Coinvariants.ker (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (actionSurjection o σ hk g) v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨x, rfl⟩ := actionSurjection_surjective o σ hk g
    exact Coinvariants.sub_mem_ker (ρ := originalRepresentation σ) x v

theorem original_index (o : Geometry.OriginalData Y T V M E Pc)
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E))
    (P : Submodule (ZMod 2) W)
    (hM : ∀ x : originalActor T V E,
      (∀ w ∈ P, originalRepresentation σ x w = w) ↔ x.val.val ∈ M)
    (hidx : (SmallModels.SymmetricThree.markerStabilizer
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) P).index = 3) :
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let H := temporaryLineNormalizer T V E
  let I₀ := originalActor T V E
  let F := SmallModels.SymmetricThree.markerStabilizer
    (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) P
  let t := actionSurjection o σ hk
  have he : F.comap t = ((lineI0 T V E ⊓ lineM M E).subgroupOf H).subgroupOf I₀ := by
    ext x
    change (∀ w ∈ P, originalRepresentation σ x w = w) ↔
      (x.val.val ∈ lineI0 T V E ∧ x.val.val ∈ lineM M E)
    rw [hM]
    exact ⟨fun hx => ⟨x.property, hx, x.val.property.1⟩, fun hx => hx.2.1⟩
  have h := F.index_comap_of_surjective (actionSurjection_surjective o σ hk)
  rw [he, hidx] at h
  change ((lineI0 T V E ⊓ lineM M E).subgroupOf H).relIndex
    ((lineI0 T V E).subgroupOf H) = 3 at h
  rwa [relIndex_subgroupOf (show lineI0 T V E ≤ H from
    (lineI0_eq_inf_temporary T V E).symm ▸ inf_le_right)] at h

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.OriginalComparison
