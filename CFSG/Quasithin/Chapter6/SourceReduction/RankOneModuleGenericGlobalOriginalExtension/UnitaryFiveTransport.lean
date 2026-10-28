module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.NativeSylowTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveRestriction
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.QuotientAction

/-!
# The original U₅ source Sylow, full local Borel and core quotient action

In the surviving plane-first marking the two source local Sylows have the
same native image U, of order 2²⁰. The full S image intersects the native
inner carrier in exactly U. Thus S∩L=S∩R, with no assertion S=T or R=O²(H).
The full native line Borel normalizes the same S image, and the original
O₂(RS) acts trivially on the line residual's SU₃(4) quotient.

These statements retain both full-overlap squares of the supplied original
extension. They establish the Sylow and quotient transports needed by the
normalized-Borel reduction. Removing the outer extension still requires
native kernel detection; the previously proved prepared U₅ completion is
a separate result and is not reproved here.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(refs/quasithin.pdf).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (M : Model 4) (e : OriginalUnitaryFive.Marking M false L R (sourceS L H))
include d h hTH hp M e

/-- Both original local Sylows map to the same native U, before collapse. -/
theorem original_unitaryFive_localSylow_images :
    (((sourceS L H ⊓ L : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map e.left =
      M.flagTwoSubgroup.map MulAut.conj) ∧
    (((sourceS L H ⊓ R : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      M.flagTwoSubgroup.map MulAut.conj) := by
  have hi := Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix
  have hind : ¬ 2 ∣ (M.flagTwoSubgroup.subgroupOf M.overlap).index := by
    change ¬ 2 ∣ M.flagTwoSubgroup.relIndex M.overlap
    rw [M.flagTwoSubgroup_relIndex_overlap]
    decide
  have he0 : (L.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map e.left =
      M.rightLocalImage.map MulAut.conj := by
    have he := d.original_local_eq_residual h hTH hp 0
    change L.subgroupOf _ = _ at he
    rw [he,e.left_residual]
    rfl
  have he1 : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      M.leftLocalImage.map MulAut.conj := by
    have he := d.original_local_eq_residual h hTH hp 1
    change R.subgroupOf _ = _ at he
    rw [he,e.right_residual]
    rfl
  have hbase : (e.left.range ⊓ e.right.range) ⊓ MulAut.innerSubgroup M.Carrier =
      M.overlap.map MulAut.conj := by
    rw [inf_inf_distrib_right,e.left_base,e.right_base,←map_inf _ _ _ hi]
    change (M.rightParabolic ⊓ M.leftParabolic).map MulAut.conj = _
    rw [inf_comm]
    rfl
  have hs0 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 :=
    le_sup_right.trans le_sup_left
  have hs1 : sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 :=
    le_sup_right.trans le_sup_left
  constructor
  · apply d.original_localSylow_image h hTH 0 e.left e.left_injective hi
      M.rightLocalImage M.overlap M.flagTwoSubgroup M.flagTwoSubgroup_isPGroup
      M.flagTwoSubgroup_le_overlap M.flagTwoSubgroup_normal_in_overlap hind
      M.flagTwoSubgroup_le_rightLocalImage he0
    rintro _ ⟨x,hx,rfl⟩
    rw [←hbase]
    refine ⟨⟨⟨x,rfl⟩,?_⟩,?_⟩
    · refine ⟨⟨x.val,hs1 hx.1⟩,?_⟩
      exact (e.agrees ⟨x.val,x.property,hs1 hx.1⟩).symm
    · exact (Subgroup.map_le_range _ _) (he0 ▸ mem_map_of_mem e.left hx.2)
  · apply d.original_localSylow_image h hTH 1 e.right e.right_injective hi
      M.leftLocalImage M.overlap M.flagTwoSubgroup M.flagTwoSubgroup_isPGroup
      M.flagTwoSubgroup_le_overlap M.flagTwoSubgroup_normal_in_overlap hind
      M.flagTwoSubgroup_le_leftLocalImage he1
    rintro _ ⟨x,hx,rfl⟩
    rw [←hbase]
    refine ⟨⟨?_,⟨x,rfl⟩⟩,?_⟩
    · refine ⟨⟨x.val,hs0 hx.1⟩,?_⟩
      exact e.agrees ⟨x.val,hs0 hx.1,x.property⟩
    · exact (Subgroup.map_le_range _ _) (he1 ▸ mem_map_of_mem e.right hx.2)
end Preparation

namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (M : Model 4) (e : OriginalUnitaryFive.Marking M false L R (sourceS L H))
include d h hTH hp M e

/-- The same native Sylow marks both original source intersections. -/
theorem original_unitaryFive_sylowHom_images :
    (((sourceS L H ⊓ L : Subgroup G).subgroupOf (sourceS L H)).map e.sylowHom =
      M.flagTwoSubgroup.map MulAut.conj) ∧
    (((sourceS L H ⊓ R : Subgroup G).subgroupOf (sourceS L H)).map e.sylowHom =
      M.flagTwoSubgroup.map MulAut.conj) := by
  have he := d.original_unitaryFive_localSylow_images h hTH hp M e
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

/-- Original U₅ markings force equality of the two actual local Sylows;
they are not identified with the whole source S or ambient T. -/
theorem original_unitaryFive_intersections : sourceS L H ⊓ L = sourceS L H ⊓ R := by
  have he := d.original_unitaryFive_sylowHom_images h hTH hp M e
  have he' := Subgroup.map_injective e.sylowHom_injective (he.1.trans he.2.symm)
  have hh := congrArg (Subgroup.map (sourceS L H).subtype) he'
  simpa only [map_subgroupOf_eq_of_le inf_le_left] using hh

/-- The size of both original local intersections is the native q¹⁰,
without a bound on the outer part of the original S. -/
theorem original_unitaryFive_intersections_card :
    Nat.card (sourceS L H ⊓ L : Subgroup G) = 2^20 ∧
    Nat.card (sourceS L H ⊓ R : Subgroup G) = 2^20 := by
  have hi := Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix
  have he := (d.original_unitaryFive_sylowHom_images h hTH hp M e).2
  have hr : Nat.card (sourceS L H ⊓ R : Subgroup G) = 2^20 := by
    have hc := congrArg (fun Q : Subgroup (MulAut M.Carrier) => Nat.card Q) he
    rw [card_map_of_injective e.sylowHom_injective,card_map_of_injective hi,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : sourceS L H ⊓ R ≤ sourceS L H)).toEquiv,
      M.flagTwoSubgroup_card] at hc
    exact hc
  exact ⟨(congrArg (fun Q : Subgroup G => Nat.card Q) (d.original_unitaryFive_intersections h hTH hp M e)).trans hr,hr⟩

/-- The original join-core acts trivially on the actual native SU₃(4)
quotient. This is the line endpoint, although it is on the source right. -/
theorem original_unitaryFive_core_quotient_action
    (g : sourceS L H) (hg : g.val ∈ (R ⊔ sourceS L H).pCoreIn 2) :
    Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction
      M.rightParabolic M.leftParabolic
      (e.sylowFlagHom (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
        M.form M.local_field_card M.conjugation M.matrix) g) = 1 := by
  let hi := Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix
  let a : Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms
      M.rightParabolic M.leftParabolic := e.sylowFlagHom hi g
  let act := Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction
    M.rightParabolic M.leftParabolic a
  apply MulEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective
    (pCore 2 (Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightResidualImage
      M.leftParabolic)) z
  change (Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction
    M.rightParabolic M.leftParabolic a) (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction_mk]
  change QuotientGroup.mk' _ (act x) = QuotientGroup.mk' _ x
  apply div_eq_one.mp
  rw [←map_div]
  apply (QuotientGroup.eq_one_iff (act x / x)).mpr
  have hh := d.original_right_core_native_action h hTH hp e hi g hg x
  apply (mem_map_iff_mem
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightResidualImage
      M.leftParabolic).subtype_injective).mp
  change (act x).val / x.val ∈
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightResidualImage
      M.leftParabolic).pCoreIn 2
  rw [show (act x).val = e.sylowHom g x.val from
    Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction_val
      M.rightParabolic M.leftParabolic a x]
  exact hh
end Preparation

namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (M : Model 4) (e : OriginalUnitaryFive.Marking M false L R (sourceS L H))
include d h hTH hp M e

/-- Exactly the native Sylow is inner in the original source S image.
The possibly larger outer source subgroup is preserved. -/
theorem original_unitaryFive_source_inner :
    e.sylowHom.range ⊓ MulAut.innerSubgroup M.Carrier =
      M.flagTwoSubgroup.map MulAut.conj := by
  have hi := Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix
  let V := e.sylowHom.range ⊓ MulAut.innerSubgroup M.Carrier
  have hV : IsPGroup 2 V :=
    ((d.hypothesisF11 h hTH).S_isP.of_surjective
      e.sylowHom.rangeRestrict e.sylowHom.rangeRestrict_surjective).to_le inf_le_left
  have hD : V ≤ M.overlap.map MulAut.conj := by
    intro a ha
    obtain ⟨s,hs⟩ := ha.1
    subst a
    have hh : e.sylowHom s ∈ (e.left.range ⊓ MulAut.innerSubgroup M.Carrier) ⊓
        (e.right.range ⊓ MulAut.innerSubgroup M.Carrier) :=
      ⟨⟨⟨_,(e.sylowHom_left s).symm⟩,ha.2⟩,⟨⟨_,rfl⟩,ha.2⟩⟩
    rw [e.left_base,e.right_base,←map_inf _ _ _ hi] at hh
    change e.sylowHom s ∈ (M.rightParabolic ⊓ M.leftParabolic).map MulAut.conj at hh
    rwa [inf_comm] at hh
  let V' := V.comap (MulAut.conj : M.Carrier →* MulAut M.Carrier)
  have hV'D : V' ≤ M.overlap := fun _ hx => (mem_map_iff_mem hi).mp (hD hx)
  have hP : IsPGroup 2 V' := hV.comap_of_injective _ hi
  let := M.flagTwoSubgroup_normal_in_overlap
  have hindex : ¬ 2 ∣ (M.flagTwoSubgroup.subgroupOf M.overlap).index := by
    change ¬ 2 ∣ M.flagTwoSubgroup.relIndex M.overlap
    rw [M.flagTwoSubgroup_relIndex_overlap]
    decide
  have hle : V' ≤ M.flagTwoSubgroup := by
    intro x hx
    exact IsPGroup.le_normal_of_index_primeTo (M.flagTwoSubgroup.subgroupOf M.overlap)
      (V'.subgroupOf M.overlap) hP.comap_subtype hindex
      (show (⟨x,hV'D hx⟩ : M.overlap) ∈ V'.subgroupOf M.overlap from hx)
  apply le_antisymm
  · intro a ha
    obtain ⟨x,_,rfl⟩ := hD ha
    exact mem_map_of_mem MulAut.conj (hle ha)
  · apply le_inf
    · rw [←(d.original_unitaryFive_sylowHom_images h hTH hp M e).2]
      exact map_le_range _ _
    · exact map_le_range _ _

/-- Both original intersections are the exact preimage of the native inner
carrier under the same S marking. -/
theorem original_unitaryFive_inner_iff (s : sourceS L H) :
    (e.sylowHom s ∈ MulAut.innerSubgroup M.Carrier ↔ s.val ∈ R) ∧
    (s.val ∈ R ↔ s.val ∈ L) := by
  have hs := d.original_unitaryFive_sylowHom_images h hTH hp M e
  have he := d.original_unitaryFive_intersections h hTH hp M e
  constructor
  · constructor
    · intro hx
      have hh : e.sylowHom s ∈ M.flagTwoSubgroup.map MulAut.conj :=
        (d.original_unitaryFive_source_inner h hTH hp M e) ▸ ⟨⟨s,rfl⟩,hx⟩
      rw [←hs.2] at hh
      exact ((mem_map_iff_mem e.sylowHom_injective).mp hh).2
    · intro hx
      have hh := mem_map_of_mem e.sylowHom
        (show s ∈ (sourceS L H ⊓ R : Subgroup G).subgroupOf (sourceS L H) from ⟨s.property,hx⟩)
      rw [hs.2] at hh
      exact map_le_range _ _ hh
  · exact ⟨fun hx => (he.ge ⟨s.property,hx⟩).2,
      fun hx => (he.le ⟨s.property,hx⟩).2⟩

/-- The native line Borel, including all its odd elements, normalizes
the original S image. This is the literal normalized-right-Borel premise. -/
theorem original_unitaryFive_borel_normalizes :
    (M.leftLocalImage ⊓ normalizer (M.flagTwoSubgroup : Set M.Carrier)).map MulAut.conj ≤
      normalizer (e.sylowHom.range : Set _) :=
  d.original_right_borel_normalizes_image h hTH hp e
    (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
      M.form M.local_field_card M.conjugation M.matrix) M.flagTwoSubgroup
    (d.original_unitaryFive_localSylow_images h hTH hp M e).2
end Preparation

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
