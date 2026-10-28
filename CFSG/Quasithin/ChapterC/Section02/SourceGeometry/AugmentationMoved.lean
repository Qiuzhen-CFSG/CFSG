module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonsplitMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.AlternatingEightCover

/-!
# The full augmentation cover of an actual C.2.7 moved section

A nonidentity fixed element of the original moved subgroup makes the
literal B.5.1 central projection noninjective. Given its A₈ natural row,
the universal cover reconstructs the entire seven-dimensional augmentation
module. The subgroup-coordinate equivalence and conjugation formula retain
the actual embedding in K R, rather than only its abstract quotient.

The A₇ source application supplies the original fixed involution z.
Selection of the A₈ row remains with qt-d-1233-natural-coordinates.
Source: Aschbacher–Smith C.2.7, B.5.1(2), I.1.5–6 and Lemma 12.3.3,
printed pp.145,99,408,808.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] (K R : Subgroup G)
  (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
  (c : NonsplitMovedConclusion
    ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
    ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))

include hCJ

omit [Finite G] in
theorem star_moved_space_eq : c.source.sectionData.space.toSubmodule =
    NormalElementaryQuotient.commutatorSpace (starV K R) (K.subgroupOf (K ⊔ R)) := by
  rw [NormalElementaryQuotient.commutatorSpace_eq (starV K R)
    (QuotientGroup.mk' (starKernel K R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _), c.source.sectionData.space_eq]
  change subspaceCommutator
    ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
    ⊤ ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))) = _
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
  rfl

/-- The coordinates of the moved section refer to the original subgroup
commutator, including its embedding in K R. -/
def star_moved_mulEquiv :
    (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) ≃*
      Multiplicative c.source.sectionData.space.toSubmodule := by
  let U := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let : IsElementaryAbelian 2 (⁅U,C⁆ : Subgroup (K ⊔ R : Subgroup G)) :=
    IsElementaryAbelian.of_le (commutator_le_left U C)
  let E := (NormalElementaryQuotient.commutatorSpaceEquiv U C).trans
    (LinearEquiv.ofEq _ _ (star_moved_space_eq K R hCJ c).symm)
  exact E.toAddEquiv.toMultiplicativeRight

omit [Finite G] in
@[simp] theorem star_moved_mulEquiv_val
    (w : (⁅starV K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))) :
    ((star_moved_mulEquiv K R hCJ c w).toAdd.val.toMul : (K ⊔ R : Subgroup G)) = w := rfl

/-- An ambient nonidentity fixed element makes the actual moved A₈ section
the entire augmentation core, with its original quotient map unchanged. -/
theorem star_moved_augmentation_coordinates
    (a : ActionEquiv
      (c.source.sectionData.action.comp
        ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (alternatingNatural 8))
    {z : G} (hz1 : z ≠ 1)
    (hz : z ∈ (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype ⊓ centralizer (K : Set G)) :
    Nonempty (c.source.sectionData.AugmentationCoordinates a) := by
  let U := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let q := QuotientGroup.mk' (starKernel K R)
  let ρ := starRepresentation K R
  let J := offenderSubgroup ρ
  obtain ⟨w,hw,hwz⟩ := hz.1
  let v : Additive U := Additive.ofMul ⟨w,commutator_le_left U C hw⟩
  have hvm : v ∈ c.source.sectionData.space.toSubmodule := by
    rw [star_moved_space_eq K R hCJ c]
    exact hw
  have hvf : v ∈ fixedSpace ρ (C.map q) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) C v).mpr
    intro k hk
    apply Subtype.ext
    change (k : G) * (w : G) = (w : G) * (k : G)
    change (w : G) = z at hwz
    rw [hwz]
    exact hz.2 k hk
  have hvf' : v ∈ fixedSpace (ρ.comp J.subtype) ((starImage K R K).subgroupOf J) := by
    intro k
    exact hvf ⟨k.val.val,k.property⟩
  have hv0 : v ≠ 0 := by
    intro he
    apply hz1
    have hh := congrArg (fun t : Additive U => ((t.toMul : U) : (K ⊔ R : Subgroup G))) he
    exact hwz.symm.trans (congrArg Subtype.val hh)
  exact c.source.sectionData.augmentationCoordinates_nonempty c.irrPlus a hvm hvf' hv0

/-- The augmentation marking on the original embedded moved subgroup.
The action formula uses actual conjugation by the original K. -/
theorem star_moved_augmentation_ambient
    (a : ActionEquiv
      (c.source.sectionData.action.comp
        ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (alternatingNatural 8))
    {z : G} (hz1 : z ≠ 1)
    (hz : z ∈ (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype ⊓ centralizer (K : Set G)) :
    let W := (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map (K ⊔ R : Subgroup G).subtype
    ∃ (π : K →* alternatingGroup (Fin 8))
      (E : W ≃* Multiplicative (BinaryPermutation.core (Fin 8))),
      Function.Surjective π ∧
      ∀ (k : K) (v w : W), (w : G) = (k : G) * (v : G) * (k : G)⁻¹ →
        (E w).toAdd = BinaryPermutation.alternatingCoreRepresentation (Fin 8) (π k) (E v).toAdd := by
  obtain ⟨d⟩ := star_moved_augmentation_coordinates K R hCJ c a hz1 hz
  let F := d.coordinates
  let U := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let W₀ := (⁅U,C⁆ : Subgroup (K ⊔ R : Subgroup G))
  let W := W₀.map (K ⊔ R : Subgroup G).subtype
  let j := W₀.equivMapOfInjective (K ⊔ R : Subgroup G).subtype (K ⊔ R : Subgroup G).subtype_injective
  let b := subgroupOfEquivOfLe hCJ
  let π := a.groupEquiv.toMonoidHom.comp (b.symm.toMonoidHom.comp (toStarImage K R))
  let m := j.symm.trans (star_moved_mulEquiv K R hCJ c)
  let E := m.trans F.toAddEquiv.toMultiplicative
  have hm (v : W) : (((m v).toAdd.val.toMul : U) : (K ⊔ R : Subgroup G)).val = (v : G) := by
    change (((star_moved_mulEquiv K R hCJ c (j.symm v)).toAdd.val.toMul : U) :
      (K ⊔ R : Subgroup G)).val = _
    rw [star_moved_mulEquiv_val]
    exact congrArg Subtype.val (j.apply_symm_apply v)
  refine ⟨π,E,a.groupEquiv.surjective.comp
    (b.symm.surjective.comp (toStarImage_surjective K R)),?_⟩
  intro k v w hw
  let k' := b.symm (toStarImage K R k)
  have hact : c.source.sectionData.space.toRepresentation k'.val (m v).toAdd = (m w).toAdd := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have ha := NormalElementaryQuotient.representation_apply U
      (QuotientGroup.mk' (starKernel K R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)
      (⟨k,mem_sup_left k.property⟩ : (K ⊔ R : Subgroup G)) (m v).toAdd.val
    have ha' := congrArg Subtype.val ha
    change _ = (k : G) * (((m v).toAdd.val.toMul : U) : (K ⊔ R : Subgroup G)).val * (k : G)⁻¹ at ha'
    rw [hm] at ha'
    exact ha'.trans (hw.symm.trans (hm w).symm)
  change F (m w).toAdd = BinaryPermutation.alternatingCoreRepresentation (Fin 8)
    (a.groupEquiv k') (F (m v).toAdd)
  exact (congrArg F hact).symm.trans (d.intertwines k' (m v).toAdd)

end CFSG.Quasithin.ChapterC.C27Source
