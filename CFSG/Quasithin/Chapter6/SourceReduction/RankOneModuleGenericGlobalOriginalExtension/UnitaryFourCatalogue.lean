module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphRigidity

/-!
# Both original U₄ endpoints in the fixed graph catalogue

Realize the prescribed native degree-two extension faithfully in Aut(U₄).
Its endpoint membership is detected on the native coordinate. The point
parabolic is self-normalizing: its characteristic solvable residual and
that residual's two-core recover it as the radical normalizer.

The exact ambient graph lift and the original index-two calculation put
all of ORIGINAL LS into the fixed extended plane. An original S-element
preserves the point parabolic, so its image belongs to the fixed extended
point as well. This identifies the two endpoint images simultaneously,
without conjugating only one endpoint or assuming that the retained LS
conjugator preserves the opposite endpoint. The existing split pair gives
surjectivity at both endpoints; the original whole-overlap equality then
restricts the SAME faithful ambient map to all three groups.

Thus the degree-two branch gives ConcreteAmalgamComparison.unitaryExtension.
Combining it with the checked ordinary branch proves the full original U₄
comparison for every selected perfect R. Both input orientations, q=4,
the full odd overlap and the original source S are retained. Exhaustive
DGS selection, the other source rows, prepared U₅, uniqueness and final
generic GlobalExit assembly are not asserted here.

Source: Aschbacher--Smith F.1.12(I)(6) and its extension argument,
printed pp.263--264; 5.2.6--7, pp.650--651 (`refs/quasithin.pdf`).
The false printed identity O₂(overlap)=U⟨σ⟩ is not used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour
namespace EndpointImages
variable (m : ℕ) (hm : 1 ≤ m)
local notation "X" => ProjectiveGroup m hm
local notation "E" => Extension.ProjectiveExtension m hm

/-- The faithful ambient action of the fixed catalogue graph extension. -/
def rho : E →* MulAut X :=
  SemidirectProduct.lift MulAut.conj (Extension.projectiveAction m hm) (by
    intro c
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    change (Extension.projectiveAction m hm c x)*y*(Extension.projectiveAction m hm c x)⁻¹ =
      Extension.projectiveAction m hm c (x*((Extension.projectiveAction m hm c)⁻¹ y)*x⁻¹)
    rw [map_mul,map_mul,map_inv]
    exact congrArg (fun z => Extension.projectiveAction m hm c x*z*(Extension.projectiveAction m hm c x)⁻¹)
      ((Extension.projectiveAction m hm c).apply_symm_apply y).symm)

theorem rho_apply (x : E) : rho m hm x = MulAut.conj x.left * Extension.projectiveAction m hm x.right := by rfl

theorem rho_inl (x : X) : rho m hm (SemidirectProduct.inl x) = MulAut.conj x := by
  simp [rho]

theorem rho_inr (c : UnitaryFourOuter.C2) :
    rho m hm (SemidirectProduct.inr c) = Extension.projectiveAction m hm c := by
  simp [rho]

theorem rho_injective : Function.Injective (rho m hm) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  change MulAut.conj x.left * Extension.projectiveAction m hm x.right=1 at hx
  rcases UnitaryFourOuter.c2_cases x.right with hr | hr
  · rw [hr,map_one,mul_one] at hx
    have hl : x.left=1 := ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
      (hx.trans (map_one _).symm)
    exact mem_bot.mpr (SemidirectProduct.ext hl hr)
  · rw [hr,Extension.projectiveAction_generator] at hx
    have he : Extension.projectiveAut m hm=MulAut.conj x.left⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hx
    exact (Extension.projectiveAut_ne_inner m hm _ he).elim

/-- Membership in either extended endpoint is detected on its native coordinate. -/
def endpoint (point : Bool) : Subgroup E :=
  if point then Extension.point m hm else Extension.plane m hm

theorem mem_endpoint (point : Bool) (x : E) :
    x ∈ endpoint m hm point ↔ x.left ∈ OriginalUnitaryFour.endpoint m hm point := by
  cases point
  · exact Extension.mem_plane m hm x
  · exact Extension.mem_point m hm x

/-- Conjugation in the actual semidirect product is its ambient native action. -/
theorem conj_inl (x : E) (y : X) :
    x * SemidirectProduct.inl y * x⁻¹ = SemidirectProduct.inl (rho m hm x y) := by
  apply (rho_injective m hm)
  rw [map_mul,map_mul,map_inv,rho_inl,rho_inl]
  apply MulEquiv.ext
  intro z
  simp [rho_apply]

/-- Every extended endpoint element preserves the entire native endpoint. -/
theorem rho_preserves (point : Bool) (x : E) (hx : x ∈ endpoint m hm point) :
    (OriginalUnitaryFour.endpoint m hm point).map (rho m hm x).toMonoidHom =
      OriginalUnitaryFour.endpoint m hm point := by
  let P := endpoint m hm point
  have hmem (x : E) (hx : x ∈ P) (y : X)
      (hy : y ∈ OriginalUnitaryFour.endpoint m hm point) :
      rho m hm x y ∈ OriginalUnitaryFour.endpoint m hm point := by
    have hy' : SemidirectProduct.inl y ∈ P := (mem_endpoint m hm point _).mpr hy
    have hh := P.mul_mem (P.mul_mem hx hy') (P.inv_mem hx)
    rw [conj_inl] at hh
    exact (mem_endpoint m hm point _).mp hh
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact hmem x hx z hz
  · intro hy
    refine ⟨rho m hm x⁻¹ y,hmem x⁻¹ (P.inv_mem hx) y hy,?_⟩
    rw [map_inv]
    exact (rho m hm x).apply_symm_apply y

/-- Preservation of the point endpoint forces preservation of its characteristic
residual radical. The latter recovers the actual point parabolic. -/
theorem point_self_normalizing (hmgt : 1 < m) :
    normalizer (pointParabolic m hm : Set X) = pointParabolic m hm := by
  apply le_antisymm _ (pointParabolic m hm).le_normalizer
  intro x hx
  let a := MulAut.conj x
  have hP : (pointParabolic m hm).map a.toMonoidHom=pointParabolic m hm := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (mem_normalizer_iff.mp hx z).mp hz
    · intro hy
      refine ⟨a.symm y,?_,a.apply_symm_apply y⟩
      apply (mem_normalizer_iff.mp hx (a.symm y)).mpr
      change a (a.symm y) ∈ pointParabolic m hm
      rw [a.apply_symm_apply]
      exact hy
  have hK : (PointLocal.ProjectiveLocal m hm).map a.toMonoidHom=PointLocal.ProjectiveLocal m hm := by
    have he := map_solvableResidual_comap a.toMonoidHom a.surjective (pointParabolic m hm)
    have hc : (pointParabolic m hm).comap a.toMonoidHom=pointParabolic m hm := by
      conv_lhs => rw [←hP]
      exact comap_map_eq_self_of_injective a.injective _
    rw [hc,PointLocal.pointParabolic_solvableResidual m hm hmgt] at he
    exact he
  have hQ : ((PointLocal.ProjectiveLocal m hm).pCoreIn 2).map a.toMonoidHom =
      (PointLocal.ProjectiveLocal m hm).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective _ _ _ a.injective,hK]
  rw [←OriginalUnitaryFour.point_core_normalizer m hm]
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · intro hy
    exact hQ.le (mem_map_of_mem a.toMonoidHom hy)
  · intro hy
    obtain ⟨z,hz,he⟩ := hQ.ge hy
    exact a.injective he ▸ hz

/-- Within the catalogue extension, preserving the point parabolic is
exactly membership in the full extended point endpoint. -/
theorem mem_point_of_preserves (hmgt : 1 < m) (x : E)
    (hx : (pointParabolic m hm).map (rho m hm x).toMonoidHom=pointParabolic m hm) :
    x ∈ Extension.point m hm := by
  let c : E := SemidirectProduct.inr x.right
  have hc : c ∈ endpoint m hm true := (mem_endpoint m hm true c).mpr (one_mem _)
  have hcg := rho_preserves m hm true c⁻¹ ((endpoint m hm true).inv_mem hc)
  change (pointParabolic m hm).map (rho m hm c⁻¹).toMonoidHom=pointParabolic m hm at hcg
  have hbase : (pointParabolic m hm).map (MulAut.conj x.left).toMonoidHom=pointParabolic m hm := by
    have he : MulAut.conj x.left = rho m hm x * rho m hm c⁻¹ := by
      rw [map_inv,show rho m hm c=Extension.projectiveAction m hm x.right from rho_inr m hm x.right,
        rho_apply,mul_inv_cancel_right]
    rw [he]
    change (pointParabolic m hm).map
      ((rho m hm x).toMonoidHom.comp (rho m hm c⁻¹).toMonoidHom)=pointParabolic m hm
    rw [←map_map,hcg,hx]
  apply (Extension.mem_point m hm x).mpr
  rw [←point_self_normalizing m hm hmgt]
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · intro hy
    exact hbase.le (mem_map_of_mem (MulAut.conj x.left).toMonoidHom hy)
  · intro hy
    obtain ⟨z,hz,he⟩ := hbase.ge hy
    exact (MulAut.conj x.left).injective he ▸ hz
/-- The native subgroup embeds with its original inner marking. -/
theorem native_le_image (point : Bool) :
    (OriginalUnitaryFour.endpoint m hm point).map MulAut.conj ≤
      (endpoint m hm point).map (rho m hm) := by
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨SemidirectProduct.inl x,(mem_endpoint m hm point _).mpr hx,rho_inl m hm x⟩

/-- A subgroup between a native endpoint and its specified degree-two extension
is the whole endpoint as soon as it contains an outer actor. -/
theorem image_eq_of_outer (point : Bool) (J : Subgroup (MulAut X))
    (hle : J ≤ (endpoint m hm point).map (rho m hm))
    (hbase : (OriginalUnitaryFour.endpoint m hm point).map MulAut.conj ≤ J)
    (a : MulAut X) (ha : a ∈ J) (hout : a ∉ MulAut.innerSubgroup X) :
    J = (endpoint m hm point).map (rho m hm) := by
  apply le_antisymm hle
  obtain ⟨x,hx,rfl⟩ := hle ha
  have hr : x.right=UnitaryFourOuter.generator :=
    (UnitaryFourOuter.c2_cases x.right).resolve_left (by
      intro hr
      apply hout
      rw [rho_apply,hr,map_one,mul_one]
      exact ⟨x.left,rfl⟩)
  have hinner : MulAut.conj x.left ∈ J := hbase (mem_map_of_mem _ ((mem_endpoint m hm point x).mp hx))
  have hg : Extension.projectiveAut m hm ∈ J := by
    have hh := J.mul_mem (J.inv_mem hinner) ha
    rw [rho_apply,hr,Extension.projectiveAction_generator,inv_mul_cancel_left] at hh
    exact hh
  rintro _ ⟨y,hy,rfl⟩
  rw [rho_apply]
  apply J.mul_mem (hbase (mem_map_of_mem _ ((mem_endpoint m hm point y).mp hy)))
  rcases UnitaryFourOuter.c2_cases y.right with hr | hr
  · rw [hr,map_one]; exact J.one_mem
  · rw [hr,Extension.projectiveAction_generator]; exact hg

private theorem range_le_of_split {Y Z : Type*} [Group Y] [Group Z]
    (D P C : Subgroup Y) (hD : D ≤ P) (hC : C ≤ P) (hgen : D ⊔ C=P)
    (f : P →* Z) (J : Subgroup Z)
    (hd : (f.comp (inclusion hD)).range ≤ J)
    (hc : ∀ x : C, f (inclusion hC x) ∈ J) : f.range ≤ J := by
  have hle : P ≤ (J.comap f).map P.subtype := by
    conv_lhs => rw [←hgen]
    apply sup_le
    · intro x hx
      exact ⟨⟨x,hD hx⟩,hd ⟨⟨x,hx⟩,rfl⟩,rfl⟩
    · intro x hx
      exact ⟨⟨x,hC hx⟩,hc ⟨x,hx⟩,rfl⟩
  rintro _ ⟨x,rfl⟩
  exact (mem_map_iff_mem P.subtype_injective).mp (hle x.property)

end EndpointImages
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open OriginalUnitaryFour.EndpointImages
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m)
  (mark : OriginalUnitaryFour.Marking m hm false L R (sourceS L H))
include d h hTH hp mark

/-- Every element of ORIGINAL LS has image in the fixed extended plane.
The exact ambient graph lift and the original index two prove this directly;
no claim that a Sylow conjugator preserves the other endpoint is needed. -/
theorem original_unitaryFour_join_catalogue
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (x : (L ⊔ sourceS L H : Subgroup G)) :
    mark.left (inclusion le_sup_left x) ∈ (Extension.plane m hm).map (rho m hm) := by
  let J := L ⊔ sourceS L H
  let f := mark.left.comp (inclusion (show J ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 from le_sup_left))
  let K := (Extension.plane m hm).map (rho m hm)
  obtain ⟨t,htL,_,ht⟩ := d.original_unitaryFour_ambient_graph_generator h hTH hp m hm mark hi
  have hidx : (L.subgroupOf J).index=2 := by
    let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes))
    have he := relIndex_sup_left ((sourceS L H).subgroupOf J) (L.subgroupOf J)
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
      (show sourceS L H ≤ J from le_sup_right),relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf (show sourceS L H ≤ J from le_sup_right)] at he
    change L.relIndex J=2
    rw [he,←inf_relIndex_right,inf_comm,d.left_intersection,hi]
  have hinner (y : J) (hy : y.val ∈ L) : f y ∈ K := by
    have hh : f y ∈ MulAut.innerSubgroup (ProjectiveGroup m hm) := by
      have hh := mark.left_residual ▸ mem_map_of_mem mark.left
        ((d.original_local_eq_residual h hTH hp 0).le
          (show (inclusion le_sup_left y : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) ∈
            L.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) from hy))
      exact map_le_range _ _ hh
    exact native_le_image m hm false (mark.left_base.le ⟨⟨inclusion le_sup_left y,rfl⟩,hh⟩)
  have htmem : f t ∈ K := by
    rw [show f t=Extension.projectiveAut m hm from ht]
    exact ⟨SemidirectProduct.inr UnitaryFourOuter.generator,
      (Extension.mem_plane m hm _).mpr (one_mem _),
      (rho_inr m hm _).trans (Extension.projectiveAction_generator m hm)⟩
  by_cases hx : x.val ∈ L
  · exact hinner x hx
  · have hxt : (x*t⁻¹).val ∈ L := (mul_mem_iff_of_index_two hidx).mpr
      (iff_of_false hx (by change t.val⁻¹ ∉ L; simpa only [inv_mem_iff] using htL))
    have he : f x=f (x*t⁻¹)*f t := by rw [←map_mul,inv_mul_cancel_right]
    change f x ∈ K
    rw [he]
    exact K.mul_mem (hinner _ hxt) htmem

/-- The SAME source actor belongs to BOTH fixed catalogue endpoints.
The right membership follows from its actual action on the point parabolic. -/
theorem original_unitaryFour_sylow_catalogue
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)
    (s : sourceS L H) :
    mark.sylowHom s ∈ (Extension.plane m hm).map (rho m hm) ∧
      mark.sylowHom s ∈ (Extension.point m hm).map (rho m hm) := by
  have hl : mark.sylowHom s ∈ (Extension.plane m hm).map (rho m hm) := by
    rw [mark.sylowHom_left]
    exact d.original_unitaryFour_join_catalogue h hTH hp m hm mark hi (inclusion le_sup_right s)
  refine ⟨hl,?_⟩
  obtain ⟨x,hx,he⟩ := hl
  refine ⟨x,mem_point_of_preserves m hm
    (d.original_unitaryFour_nonbinary h hTH hp m hm false mark) x ?_,he⟩
  rw [he]
  exact (mark.sylowFlagHom (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm) s).property.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open OriginalUnitaryFour.EndpointImages
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m)
  (mark : OriginalUnitaryFour.Marking m hm false L R (sourceS L H))
include d h hTH hp mark

/-- Both full source endpoint images are the FIXED catalogue endpoints,
under one faithful ambient homomorphism. -/
theorem original_unitaryFour_endpoint_images
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    mark.left.range=(Extension.plane m hm).map (rho m hm) ∧
      mark.right.range=(Extension.point m hm).map (rho m hm) := by
  obtain ⟨t,hout,ht,_,_⟩ := d.original_unitaryFour_source_ambient_graph h hTH hp m hm false mark hi
  let P i := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let D i := ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i
  let C := zpowers t.val
  have hc : C ≤ sourceS L H := zpowers_le.mpr t.property
  have hCP (i : Fin 2) : C ≤ P i := hc.trans (le_sup_right.trans le_sup_left)
  have hsplit (i : Fin 2) := d.original_unitaryFour_split_endpoints h hTH hp m hm false mark hi t hout ht i
  have himages := d.original_unitaryFour_reduced_images h hTH hp m hm false mark
  have hleft : mark.left.range ≤ (Extension.plane m hm).map (rho m hm) := by
    apply range_le_of_split (D 0) (P 0) C
      (d.originalUnitaryFour_reduced_le h hTH hp m hm false mark 0) (hCP 0) (hsplit 0).1 mark.left
    · rw [himages.1]
      exact native_le_image m hm false
    · intro x
      have he := mark.sylowHom_left (⟨x.val,hc x.property⟩ : sourceS L H)
      exact he ▸ (d.original_unitaryFour_sylow_catalogue h hTH hp m hm mark hi ⟨x.val,hc x.property⟩).1
  have hright : mark.right.range ≤ (Extension.point m hm).map (rho m hm) := by
    apply range_le_of_split (D 1) (P 1) C
      (d.originalUnitaryFour_reduced_le h hTH hp m hm false mark 1) (hCP 1) (hsplit 1).1 mark.right
    · rw [himages.2]
      exact native_le_image m hm true
    · intro x
      exact (d.original_unitaryFour_sylow_catalogue h hTH hp m hm mark hi ⟨x.val,hc x.property⟩).2
  have hout' := (d.original_unitaryFour_split_actor h hTH hp m hm false mark t hout ht).2
  constructor
  · apply image_eq_of_outer m hm false mark.left.range hleft
      (mark.left_base.symm.le.trans inf_le_left) (mark.sylowHom t) _ hout'
    rw [mark.sylowHom_left]
    exact ⟨_,rfl⟩
  · exact image_eq_of_outer m hm true mark.right.range hright
      (mark.right_base.symm.le.trans inf_le_left) (mark.sylowHom t) ⟨_,rfl⟩ hout'
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.EndpointImages
variable {X Y Z : Type*} [Group X] [Group Y] [Group Z]
private def imageEquiv (f : X →* Z) (hf : Function.Injective f)
    (j : Y →* Z) (hj : Function.Injective j) (P : Subgroup Y)
    (he : f.range=P.map j) : X ≃* P :=
  (MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr he).trans
    (P.equivMapOfInjective j hj).symm)

private theorem imageEquiv_apply (f : X →* Z) (hf : Function.Injective f)
    (j : Y →* Z) (hj : Function.Injective j) (P : Subgroup Y)
    (he : f.range=P.map j) (x : X) : j (imageEquiv f hf j hj P he x).val=f x :=
  congrArg Subtype.val ((P.equivMapOfInjective j hj).apply_symm_apply _)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalUnitaryFour.EndpointImages

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open OriginalUnitaryFour.EndpointImages
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m)
  (mark : OriginalUnitaryFour.Marking m hm false L R (sourceS L H))
  (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2)

/-- The original full amalgam is the fixed graph extension, with both endpoint
maps and the entire odd Borel restricted through one faithful ambient action. -/
def originalUnitaryFourExtensionComparison :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (Extension.amalgam m hm).reverse := by
  have hl := (d.original_unitaryFour_endpoint_images h hTH hp m hm mark hi).1
  have hr := (d.original_unitaryFour_endpoint_images h hTH hp m hm mark hi).2
  let fm := mark.left.comp (sourceParabolicAmalgam ![L,R] (sourceS L H)).left
  have hfm : Function.Injective fm := mark.left_injective.comp (inclusion_injective inf_le_left)
  have hmid : fm.range=(Extension.overlap m hm).map (rho m hm) := by
    rw [show fm.range=mark.left.range ⊓ mark.right.range from mark.whole_overlap,
      hl,hr,←map_inf _ _ _ (rho_injective m hm),inf_comm,Extension.exact_overlap]
  refine { left := imageEquiv mark.left mark.left_injective (rho m hm) (rho_injective m hm) _ hl
           middle := imageEquiv fm hfm (rho m hm) (rho_injective m hm) _ hmid
           right := imageEquiv mark.right mark.right_injective (rho m hm) (rho_injective m hm) _ hr
           left_commutes := ?_
           right_commutes := ?_ }
  · intro x
    apply Subtype.ext
    apply rho_injective m hm
    exact (imageEquiv_apply mark.left mark.left_injective (rho m hm) (rho_injective m hm) _ hl _).trans
      (imageEquiv_apply fm hfm (rho m hm) (rho_injective m hm) _ hmid x).symm
  · intro x
    apply Subtype.ext
    apply rho_injective m hm
    exact (imageEquiv_apply mark.right mark.right_injective (rho m hm) (rho_injective m hm) _ hr _).trans
      ((mark.agrees x).symm.trans
        (imageEquiv_apply fm hfm (rho m hm) (rho_injective m hm) _ hmid x).symm)

theorem originalUnitaryFourExtensionComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    rho m hm ((d.originalUnitaryFourExtensionComparison h hTH hp m hm mark hi).left x).val=mark.left x :=
  imageEquiv_apply _ _ _ _ _ _ x

theorem originalUnitaryFourExtensionComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    rho m hm ((d.originalUnitaryFourExtensionComparison h hTH hp m hm mark hi).right x).val=mark.right x :=
  imageEquiv_apply _ _ _ _ _ _ x

theorem originalUnitaryFourExtensionComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    rho m hm ((d.originalUnitaryFourExtensionComparison h hTH hp m hm mark hi).middle x).val=
      mark.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  imageEquiv_apply _ _ _ _ _ _ x
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark

/-- Either input orientation gives the actual reversed catalogue extension;
the original local hypotheses determine the admissible orientation. -/
theorem original_unitaryFour_amalgam_of_index_two
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (Extension.amalgam m hm).reverse) := by
  have ho := d.original_unitaryFour_orientation h hTH hp m hm point mark
  subst point
  exact ⟨d.originalUnitaryFourExtensionComparison h hTH hp m hm mark hi⟩

/-- The exceptional degree-two U₄ row supplies an actual concrete comparison. -/
theorem concreteComparison_of_original_unitaryFour_index_two
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) :=
  .unitaryExtension m hm (Or.inr
    (d.original_unitaryFour_amalgam_of_index_two h hTH hp m hm point mark hi))

/-- The full original U₄ row, for EVERY selected perfect R, has its ordinary
or specified graph-extension comparison with no action or endpoint premise. -/
theorem original_unitaryFour_amalgam_alternatives :
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (amalgam m hm).reverse) ∨
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (Extension.amalgam m hm).reverse) := by
  rcases d.original_unitaryFour_outer_index_one_or_two h hTH hp m hm point mark with hi | hi
  · exact Or.inl (d.original_unitaryFour_amalgam_of_index_one h hTH hp m hm point mark hi)
  · exact Or.inr (d.original_unitaryFour_amalgam_of_index_two h hTH hp m hm point mark hi)

theorem concreteComparison_of_original_unitaryFour :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  rcases d.original_unitaryFour_amalgam_alternatives h hTH hp m hm point mark with he | he
  · exact .unitary m hm (Or.inr he)
  · exact .unitaryExtension m hm (Or.inr he)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
