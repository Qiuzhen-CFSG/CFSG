module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourRestriction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.NativeSylowTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryReduction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry

/-!
# Original U₄ Sylows and normalized Borel transport

The broad original marking excludes q=2 using both perfect nontrivial source
factors. For q>2, each source local Sylow maps to the native unipotent subgroup
U of order q⁶, by relative Sylow maximality in the marked native residual.
Consequently S∩L=S∩R=T∩L, and the inner part of the original S image is exactly U.
The full right local Borel normalizes that image, retaining its odd elements.

Removing S from the two endpoints gives precisely their two-residuals O²(Pᵢ).
No bound on the remaining outer part is imposed: both orientations, q=4 and
the degree-two U₄ extension are retained. The adjacent reduced comparison
restricts these same markings and applies native involution placement.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, and 5.2.6--7,
pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalUnitaryFour
open ChapterF.GreenBook.LieModels.UnitaryFour

@[expose] def nativeResidual (m : ℕ) (hm : 1 ≤ m) (point : Bool) : Subgroup (ProjectiveGroup m hm) :=
  (solvableResidual (endpoint m hm point)).map (endpoint m hm point).subtype

private theorem binary_point_solvable : Group.IsSolvable (pointParabolic 1 (Nat.le_refl 1)) := by
  let := PointLocal.matrixLocal_isSolvable_two
  have hsol : Group.IsSolvable (pointParabolicMatrix 1 (Nat.le_refl 1)) := by
    apply Group.isSolvable_of_ker_le_range
      (inclusion (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal.localSU_le_pointParabolicSU (MatrixField 1) (standardForm 1 (Nat.le_refl 1))))
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.pointScalarUnits (MatrixField 1) (standardForm 1 (Nat.le_refl 1)))
    rw [inclusion_range, Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.pointScalarUnits_ker]
  let := hsol
  let e : pointParabolicMatrix 1 (Nat.le_refl 1) ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective (projection 1 (Nat.le_refl 1))
      (projection_injective 1 (Nat.le_refl 1))
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem upper_le_residual (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) (point : Bool) :
    upperProjective m hm ≤ nativeResidual m hm point := by
  cases point
  · let := L2_isPerfect m hm
    exact (two_subgroup_le_L2 m hm _ (projectiveSylow m hm).isPGroup'
      (projectiveSylow_le_parabolics m hm).2).trans
        (le_map_solvableResidual_of_isPerfect _ _ (L2_le_planeParabolic m hm))
  · change upperProjective m hm ≤ (solvableResidual (pointParabolic m hm)).map (pointParabolic m hm).subtype
    rw [PointLocal.pointParabolic_solvableResidual m hm hmgt]
    exact upperProjective_le_pointLocal m hm

end OriginalUnitaryFour
namespace Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp e

/-- Both original factors are nonsolvable, so the binary point residual
cannot occur in either orientation of the broad marking. -/
theorem original_unitaryFour_nonbinary : 1 < m := by
  have nonsolvable (i : Fin 2) : ¬ Group.IsSolvable (![L,R] i) := by
    fin_cases i
    · exact Chapter1.mem_L_not_isSolvable h.local_mem.1.1
    · let := hp
      let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr (fun hh => d.right_outside (hh ▸ bot_le))
      exact Group.IsPerfect.not_isSolvable R
  have excludes (i : Fin 2)
      (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* MulAut (ProjectiveGroup 1 (by decide)))
      (hf : Function.Injective f)
      (hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
        ((solvableResidual (pointParabolic 1 (by decide))).map (pointParabolic 1 (by decide)).subtype).map MulAut.conj) : False := by
    let j := MulAut.conj.comp (pointParabolic 1 (by decide)).subtype
    have hj : Function.Injective j :=
      (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective 1 (by decide)).comp Subtype.val_injective
    let a := d.originalEndpointResidualEquiv h hTH hp i f hf j hj (by simpa only [map_map] using hr)
    let := OriginalUnitaryFour.binary_point_solvable
    exact nonsolvable i (Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective)
  by_contra hsmall
  have hm1 : m = 1 := by omega
  subst m
  cases point
  · exact excludes 1 e.right e.right_injective e.right_residual
  · exact excludes 0 e.left e.left_injective e.left_residual

/-- Both relative source Sylows have exactly the native unipotent image,
using their actual domains in the two full source endpoints. -/
theorem original_unitaryFour_localSylow_images :
    (((sourceS L H ⊓ L : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map e.left =
      (upperProjective m hm).map MulAut.conj) ∧
    (((sourceS L H ⊓ R : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      (upperProjective m hm).map MulAut.conj) := by
  have hi := ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
  have hmgt := d.original_unitaryFour_nonbinary h hTH hp m hm point e
  have hind : ¬ 2 ∣ ((upperProjective m hm).subgroupOf (overlap m hm)).index :=
    ((projectiveSylow m hm).subtype (upperProjective_le_overlap m hm)).not_dvd_index
  have he0 : (L.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map e.left =
      (OriginalUnitaryFour.nativeResidual m hm point).map MulAut.conj := by
    have he := d.original_local_eq_residual h hTH hp 0
    change L.subgroupOf _ = _ at he
    rw [he,e.left_residual]
    rfl
  have he1 : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      (OriginalUnitaryFour.nativeResidual m hm (!point)).map MulAut.conj := by
    have he := d.original_local_eq_residual h hTH hp 1
    change R.subgroupOf _ = _ at he
    rw [he,e.right_residual]
    rfl
  have hbase : (e.left.range ⊓ e.right.range) ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm) =
      (overlap m hm).map MulAut.conj := by
    rw [inf_inf_distrib_right,e.left_base,e.right_base,←map_inf _ _ _ hi]
    cases point
    · change (planeParabolic m hm ⊓ pointParabolic m hm).map MulAut.conj = _
      rw [inf_comm,exact_overlap]
    · change (pointParabolic m hm ⊓ planeParabolic m hm).map MulAut.conj = _
      rw [exact_overlap]
  have hs0 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 :=
    le_sup_right.trans le_sup_left
  have hs1 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 :=
    le_sup_right.trans le_sup_left
  constructor
  · apply d.original_localSylow_image h hTH 0 e.left e.left_injective hi
      (OriginalUnitaryFour.nativeResidual m hm point) (overlap m hm) (upperProjective m hm)
      (projectiveSylow m hm).isPGroup' (upperProjective_le_overlap m hm)
      (upperProjective_normal_in_overlap m hm) hind
      (OriginalUnitaryFour.upper_le_residual m hm hmgt point) he0
    rintro _ ⟨x,hx,rfl⟩
    rw [←hbase]
    refine ⟨⟨⟨x,rfl⟩,?_⟩,?_⟩
    · refine ⟨⟨x.val,hs1 hx.1⟩,?_⟩
      exact (e.agrees ⟨x.val,x.property,hs1 hx.1⟩).symm
    · exact (Subgroup.map_le_range _ _) (he0 ▸ mem_map_of_mem e.left hx.2)
  · apply d.original_localSylow_image h hTH 1 e.right e.right_injective hi
      (OriginalUnitaryFour.nativeResidual m hm (!point)) (overlap m hm) (upperProjective m hm)
      (projectiveSylow m hm).isPGroup' (upperProjective_le_overlap m hm)
      (upperProjective_normal_in_overlap m hm) hind
      (OriginalUnitaryFour.upper_le_residual m hm hmgt (!point)) he1
    rintro _ ⟨x,hx,rfl⟩
    rw [←hbase]
    refine ⟨⟨?_,⟨x,rfl⟩⟩,?_⟩
    · refine ⟨⟨x.val,hs0 hx.1⟩,?_⟩
      exact e.agrees ⟨x.val,hs0 hx.1,x.property⟩
    · exact (Subgroup.map_le_range _ _) (he1 ▸ mem_map_of_mem e.right hx.2)
/-- The same native Sylow marks both original source intersections. -/
theorem original_unitaryFour_sylowHom_images :
    (((sourceS L H ⊓ L : Subgroup G).subgroupOf (sourceS L H)).map e.sylowHom =
      (upperProjective m hm).map MulAut.conj) ∧
    (((sourceS L H ⊓ R : Subgroup G).subgroupOf (sourceS L H)).map e.sylowHom =
      (upperProjective m hm).map MulAut.conj) := by
  have he := d.original_unitaryFour_localSylow_images h hTH hp m hm point e
  have hs0 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 :=
    le_sup_right.trans le_sup_left
  have hs1 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 :=
    le_sup_right.trans le_sup_left
  constructor
  · rw [←he.1]
    ext a
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s.val,hs0 s.property⟩,hs,(e.sylowHom_left s).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx.1⟩,hx,e.sylowHom_left ⟨x.val,hx.1⟩⟩
  · rw [←he.2]
    ext a
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s.val,hs1 s.property⟩,hs,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx.1⟩,hx,rfl⟩

/-- Original U₄ markings force equality of the two actual local Sylows;
they are not identified with the whole source S or ambient T. -/
theorem original_unitaryFour_intersections : sourceS L H ⊓ L = sourceS L H ⊓ R := by
  have he := d.original_unitaryFour_sylowHom_images h hTH hp m hm point e
  have he' := Subgroup.map_injective e.sylowHom_injective (he.1.trans he.2.symm)
  have hh := congrArg (Subgroup.map (sourceS L H).subtype) he'
  simpa only [map_subgroupOf_eq_of_le inf_le_left] using hh

/-- The size of both original local intersections is the native q⁶,
without a bound on the outer part of the original S. -/
theorem original_unitaryFour_intersections_card :
    Nat.card (sourceS L H ⊓ L : Subgroup G) = (2^m)^6 ∧
    Nat.card (sourceS L H ⊓ R : Subgroup G) = (2^m)^6 := by
  have hi := ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
  have he := (d.original_unitaryFour_sylowHom_images h hTH hp m hm point e).2
  have hr : Nat.card (sourceS L H ⊓ R : Subgroup G) = (2^m)^6 := by
    have hc := congrArg (fun Q : Subgroup (MulAut (ProjectiveGroup m hm)) => Nat.card Q) he
    rw [card_map_of_injective e.sylowHom_injective,card_map_of_injective hi,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : sourceS L H ⊓ R ≤ sourceS L H)).toEquiv,
      upperProjective_card] at hc
    exact hc
  exact ⟨(congrArg (fun Q : Subgroup G => Nat.card Q) (d.original_unitaryFour_intersections h hTH hp m hm point e)).trans hr,hr⟩

/-- Exactly the native Sylow is inner in the original source S image.
The possibly larger outer source subgroup is preserved. -/
theorem original_unitaryFour_source_inner :
    e.sylowHom.range ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm) =
      (upperProjective m hm).map MulAut.conj := by
  have hi := ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
  let V := e.sylowHom.range ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm)
  have hV : IsPGroup 2 V :=
    ((d.hypothesisF11 h hTH).S_isP.of_surjective
      e.sylowHom.rangeRestrict e.sylowHom.rangeRestrict_surjective).to_le inf_le_left
  have hD : V ≤ (overlap m hm).map MulAut.conj := by
    intro a ha
    obtain ⟨s,hs⟩ := ha.1
    subst a
    have hh : e.sylowHom s ∈ (e.left.range ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm)) ⊓
        (e.right.range ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm)) :=
      ⟨⟨⟨_,(e.sylowHom_left s).symm⟩,ha.2⟩,⟨⟨_,rfl⟩,ha.2⟩⟩
    rw [e.left_base,e.right_base,←map_inf _ _ _ hi] at hh
    change e.sylowHom s ∈ ((OriginalUnitaryFour.endpoint m hm point) ⊓
      (OriginalUnitaryFour.endpoint m hm (!point))).map MulAut.conj at hh
    cases point
    · change e.sylowHom s ∈ (planeParabolic m hm ⊓ pointParabolic m hm).map MulAut.conj at hh
      rwa [inf_comm,exact_overlap] at hh
    · change e.sylowHom s ∈ (pointParabolic m hm ⊓ planeParabolic m hm).map MulAut.conj at hh
      rwa [exact_overlap] at hh
  let V' := V.comap (MulAut.conj : (ProjectiveGroup m hm) →* MulAut (ProjectiveGroup m hm))
  have hV'D : V' ≤ (overlap m hm) := fun _ hx => (mem_map_iff_mem hi).mp (hD hx)
  have hP : IsPGroup 2 V' := hV.comap_of_injective _ hi
  let := upperProjective_normal_in_overlap m hm
  have hindex : ¬ 2 ∣ ((upperProjective m hm).subgroupOf (overlap m hm)).index :=
    ((projectiveSylow m hm).subtype (upperProjective_le_overlap m hm)).not_dvd_index
  have hle : V' ≤ (upperProjective m hm) := by
    intro x hx
    exact IsPGroup.le_normal_of_index_primeTo ((upperProjective m hm).subgroupOf (overlap m hm))
      (V'.subgroupOf (overlap m hm)) hP.comap_subtype hindex
      (show (⟨x,hV'D hx⟩ : (overlap m hm)) ∈ V'.subgroupOf (overlap m hm) from hx)
  apply le_antisymm
  · intro a ha
    obtain ⟨x,_,rfl⟩ := hD ha
    exact mem_map_of_mem MulAut.conj (hle ha)
  · apply le_inf
    · rw [←(d.original_unitaryFour_sylowHom_images h hTH hp m hm point e).2]
      exact map_le_range _ _
    · exact map_le_range _ _

/-- Both original intersections are the exact preimage of the native inner
carrier under the same S marking. -/
theorem original_unitaryFour_inner_iff (s : sourceS L H) :
    (e.sylowHom s ∈ MulAut.innerSubgroup (ProjectiveGroup m hm) ↔ s.val ∈ R) ∧
    (s.val ∈ R ↔ s.val ∈ L) := by
  have hs := d.original_unitaryFour_sylowHom_images h hTH hp m hm point e
  have he := d.original_unitaryFour_intersections h hTH hp m hm point e
  constructor
  · constructor
    · intro hx
      have hh : e.sylowHom s ∈ (upperProjective m hm).map MulAut.conj :=
        (d.original_unitaryFour_source_inner h hTH hp m hm point e) ▸ ⟨⟨s,rfl⟩,hx⟩
      rw [←hs.2] at hh
      exact ((mem_map_iff_mem e.sylowHom_injective).mp hh).2
    · intro hx
      have hh := mem_map_of_mem e.sylowHom
        (show s ∈ (sourceS L H ⊓ R : Subgroup G).subgroupOf (sourceS L H) from ⟨s.property,hx⟩)
      rw [hs.2] at hh
      exact map_le_range _ _ hh
  · exact ⟨fun hx => (he.ge ⟨s.property,hx⟩).2,
      fun hx => (he.le ⟨s.property,hx⟩).2⟩

/-- The native right local Borel, including all its odd elements, normalizes
the original S image. This is the literal normalized-right-Borel premise. -/
theorem original_unitaryFour_borel_normalizes :
    ((OriginalUnitaryFour.nativeResidual m hm (!point)) ⊓ normalizer ((upperProjective m hm) : Set (ProjectiveGroup m hm))).map MulAut.conj ≤
      normalizer (e.sylowHom.range : Set _) :=
  d.original_right_borel_normalizes_image h hTH hp e
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm) (upperProjective m hm)
    (d.original_unitaryFour_localSylow_images h hTH hp m hm point e).2

/-- The literal reduced source endpoints are the two-residuals of the
original full endpoints, before bounding the outer extension. -/
theorem original_unitaryFour_reduced_parabolics (i : Fin 2) :
    ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i =
      (pResidual 2 (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map
        (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype := by
  have hs := d.original_unitaryFour_intersections h hTH hp m hm point e
  have hsi : ∀ i : Fin 2, sourceS L H ⊓ ![L,R] i = (T : Subgroup G) ⊓ L := by
    intro i
    fin_cases i
    · exact d.left_intersection
    · exact hs.symm.trans d.left_intersection
  have hri (i : Fin 2) : (T : Subgroup G) ⊓ L ≤ ![L,R] i := by
    rw [←hsi i]
    exact inf_le_right
  rw [d.reducedParabolic_eq_twoResidual h hTH hp hs i]
  change ![L,R] i ⊔ ((T : Subgroup G) ⊓ L) ⊔
    ChapterF.Source.borel (![L,R] (ChapterF.Source.other i)) ((T : Subgroup G) ⊓ L) = _
  rw [sup_eq_left.mpr (hri i)]
  unfold reducedParabolic ChapterF.Source.borel
  rw [inf_eq_left.mpr (hri _),hsi]
end Preparation

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
