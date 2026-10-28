module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Independent
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Kernel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.Generation

/-!
# Full product image and its exact kernel

Independent Baumann parity and a genuine T-plane exchange generate both sign
coordinates. Together with the actual cubic rotation image this gives the full
base S₃ × S₃. The original conjugation action therefore defines a surjection
from XS with kernel exactly O₂(XS), retaining its pointwise isometry action.

Source: Aschbacher–Smith, 15.4.12(6), printed pp.1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

theorem SourceAction.join_le (d : SourceAction T M X) (h : Input K T M X 2) :
    X ⊔ ChapterB.baumann (T : Subgroup G) ≤ M :=
  sup_le d.member_le (inf_le_left.trans h.sylow_le)

theorem SourceAction.join_image (d : SourceAction T M X) (h : Input K T M X 2) :
    ((X ⊔ ChapterB.baumann (T : Subgroup G)).subgroupOf M).map d.actor = base := by
  let S := ChapterB.baumann (T : Subgroup G)
  let D := ((X ⊔ S).subgroupOf M).map d.actor
  have hSM : S ≤ M := inf_le_left.trans h.sylow_le
  have hD : D ≤ base := by
    change ((X ⊔ S).subgroupOf M).map d.actor ≤ _
    rw [subgroupOf_sup d.member_le hSM, Subgroup.map_sup, d.cubic_image]
    exact sup_le Concrete.rotations_le_base (map_le_iff_le_comap.mpr d.baumann_base)
  have hR : rotations ≤ D := by
    rw [← d.cubic_image]
    exact map_mono (subgroupOf_mono M le_sup_left)
  obtain ⟨b,hb⟩ := d.exists_independent_parity h
  obtain ⟨t,ht⟩ := d.exists_swap h
  have hbD : d.actor b ∈ D := mem_map.mpr ⟨b,(le_sup_right : S ≤ X ⊔ S) b.property,rfl⟩
  have hnS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_baumann _)
  let m := inclusion h.sylow_le t
  have hconj : d.actor m * d.actor b * (d.actor m)⁻¹ ∈ D := by
    have hs : ((m : M) : G) * ((b : M) : G) * (((m : M) : G))⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (hnS t.property) (b : G)).mp b.property
    refine mem_map.mpr ⟨m * b * m⁻¹, (le_sup_right : S ≤ X ⊔ S) hs, ?_⟩
    rw [map_mul, map_mul, map_inv]
  exact Concrete.base_generated_of_independent_parity D hD hR
    (d.actor b) (d.actor m) hbD hb ht hconj

noncomputable def SourceAction.productMap (d : SourceAction T M X) (h : Input K T M X 2) :
    (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) →*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  Concrete.baseEquiv.toMonoidHom.comp
    ((d.actor.comp (inclusion (d.join_le h))).codRestrict
      base (by
        intro x
        exact (d.join_image h).le (mem_map.mpr ⟨inclusion (d.join_le h) x,x.property,rfl⟩)))

theorem SourceAction.productMap_surjective (d : SourceAction T M X) (h : Input K T M X 2) :
    Function.Surjective (d.productMap h) := by
  intro y
  let b := Concrete.baseEquiv.symm y
  have hb : b.val ∈ ((X ⊔ ChapterB.baumann (T : Subgroup G)).subgroupOf M).map d.actor :=
    (d.join_image h).ge b.property
  obtain ⟨m,hm,he⟩ := hb
  let x : (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) := ⟨m,hm⟩
  refine ⟨x, ?_⟩
  change Concrete.baseEquiv _ = y
  rw [show y = Concrete.baseEquiv b from (Concrete.baseEquiv.apply_symm_apply y).symm]
  apply congrArg Concrete.baseEquiv
  exact Subtype.ext he

theorem SourceAction.productMap_kernel (d : SourceAction T M X) (h : Input K T M X 2) :
    (d.productMap h).ker = pCore 2 (X ⊔ ChapterB.baumann (T : Subgroup G) : Subgroup G) := by
  apply product_kernel_eq_core _ (d.productMap_surjective h)
  have he : (d.productMap h).ker = (d.actor.comp (inclusion
      (sup_le d.member_le (inf_le_left.trans h.sylow_le)))).ker := by
    ext x
    change Concrete.baseEquiv _ = 1 ↔ d.actor _ = 1
    rw [←map_one Concrete.baseEquiv, Concrete.baseEquiv.injective.eq_iff]
    exact Subtype.ext_iff
  rw [he]
  exact d.join_kernel_isPGroup h

theorem SourceAction.productMap_action (d : SourceAction T M X) (h : Input K T M X 2) :
    Concrete.productIsometry.comp (d.productMap h) =
      d.actor.comp (inclusion (d.join_le h)) := by
  apply MonoidHom.ext
  intro x
  change (Concrete.baseEquiv.symm (Concrete.baseEquiv _)).val = _
  rw [Concrete.baseEquiv.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
