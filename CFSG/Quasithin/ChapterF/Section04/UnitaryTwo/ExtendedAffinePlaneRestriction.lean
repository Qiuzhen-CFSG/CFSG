module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane
public import Theory.Representation.BinaryAlternatingFiveExtension.IndexTwo
public import Theory.GroupTheory.CompatibleRestriction
/-!
# Compatible ordinary and doubled unitary plane comparisons

The affine alternating-five group is the unique subgroup of index two in the
symmetric affine group containing all translations. Consequently the marked
full-plane comparison carries this subgroup onto the literal ordinary plane.
Restricting the same comparison gives an ordinary map with the same marked
root, core and overlap, together with its exact inclusion square.

These comparisons and the intrinsic index-two characterization supply the
plane restriction used in the doubled source amalgam of Aschbacher--Smith
13.5.17, printed p.922.
-/

open Subgroup
public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation AlternatingFiveExtension OverlapFactorizationExtension
local notation "hn" => Nat.le_refl 1
local notation "P" => planeParabolic 1 hn
local notation "PE" => Extension.plane 1 hn
local notation "A" => AlternatingModel
local notation "S" => SymmetricModel
local notation "V" => Multiplicative (core (Fin 5))
local notation "Z" => SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)
local notation "j" => Extension.binaryPlaneInclusion

/-- The ordinary plane has index two in its literal extension. -/
theorem ordinaryPlane_index : (j).range.index = 2 := by
  have hc : Nat.card (j).range = 960 :=
    (Nat.card_congr (MonoidHom.ofInjective Extension.binaryPlaneInclusion_injective).toEquiv).symm.trans
      BinaryCompletion.plane_card
  have h := (j).range.index_mul_card
  rw [hc,Extension.binary_plane_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 960) (h.trans (by decide))


/-- Every full comparison preserving translations carries the ordinary subgroup onto the ordinary plane. -/
theorem map_symmetricEmbedding_range (E : S ≃* PE)
    (hV : (SemidirectProduct.inl : V →* S).range.map E.toMonoidHom=planeCore) :
    symmetricEmbedding.range.map E.toMonoidHom=(j).range := by
  let K := (j).range.map E.symm.toMonoidHom
  have hK : K=symmetricEmbedding.range := by
    apply eq_symmetricEmbedding_range_of_index_two K
    · rintro _ ⟨v,rfl⟩
      have hv : E (SemidirectProduct.inl v) ∈ planeCore := by
        rw [←hV]
        exact mem_map_of_mem _ ⟨v,rfl⟩
      have hv' : E (SemidirectProduct.inl v) ∈ (j).range := by
        rcases hv with ⟨x,hx,hxx⟩
        exact ⟨x,hxx⟩
      exact ⟨E (SemidirectProduct.inl v),hv',E.symm_apply_apply _⟩
    · exact ((j).range.index_map_equiv E.symm).trans ordinaryPlane_index
  rw [←hK]
  change ((j).range.map E.symm.toMonoidHom).map E.toMonoidHom=(j).range
  rw [map_map]
  have he : E.toMonoidHom.comp E.symm.toMonoidHom = MonoidHom.id PE := by
    apply MonoidHom.ext
    intro x
    exact E.apply_symm_apply x
  rw [he,map_id]

/-- Compatible full and ordinary affine comparisons, with all root, core and overlap markings. -/
theorem exists_compatible_marked_plane_equivs : ∃ (E : S ≃* PE) (E0 : A ≃* P),
    E (Z : S) = longRight ∧
    (SemidirectProduct.inl : V →* S).range.map E.toMonoidHom = planeCore ∧
    (centralizer ({Z} : Set S)).map E.toMonoidHom =
      (Extension.overlap 1 hn).subgroupOf PE ∧
    E0 (Z : A) = ModelClasses.longRight ∧
    (SemidirectProduct.inl : V →* A).range.map E0.toMonoidHom = pCore 2 P ∧
    borelEmbedding.range.map E0.toMonoidHom = (overlap 1 hn).subgroupOf P ∧
    ∀ x, E (symmetricEmbedding x) = j (E0 x) := by
  obtain ⟨E,hz,hV,hB⟩ := exists_marked_plane_equiv
  obtain ⟨E0,hcomp⟩ := MulEquiv.exists_compatible_restriction symmetricEmbedding
    symmetricEmbedding_injective j Extension.binaryPlaneInclusion_injective E
    (map_symmetricEmbedding_range E hV)
  have hz0 : E0 (Z : A)=ModelClasses.longRight := by
    apply Extension.binaryPlaneInclusion_injective
    rw [←hcomp,symmetricEmbedding_inl,hz]
    rfl
  obtain ⟨e,hez,heV,heB⟩ := AffinePlane.exists_marked_plane_equiv
  have hcore : (SemidirectProduct.inl : V →* A).range = pCore 2 A := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [heV,pCore_map_iso]
  refine ⟨E,E0,hz,hV,hB,hz0,?_,?_,hcomp⟩
  · rw [hcore,pCore_map_iso]
  · rw [borelEmbedding_range]
    have hc : (centralizer ({Z} : Set A)).map E0.toMonoidHom =
        centralizer ({ModelClasses.longRight} : Set P) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [←hz0,mem_centralizer_singleton_iff]
        exact (map_mul E0 _ _).symm.trans
          ((congrArg E0 (mem_centralizer_singleton_iff.mp hx)).trans (map_mul E0 _ _))
      · intro hy
        refine ⟨E0.symm y,?_,E0.apply_symm_apply y⟩
        apply mem_centralizer_singleton_iff.mpr
        apply E0.injective
        rw [map_mul,map_mul,E0.apply_symm_apply,hz0]
        exact mem_centralizer_singleton_iff.mp hy
    rw [hc,ModelClasses.right_long_centralizer,←exact_overlap,inf_subgroupOf_right]

/-- Any index-two subgroup containing the plane core is the ordinary plane. -/
theorem eq_ordinary_of_index_two (K : Subgroup PE)
    (hV : planeCore ≤ K) (hindex : K.index=2) : K=(j).range := by
  obtain ⟨E,hz,hcore,hB⟩ := exists_marked_plane_equiv
  have hK : K.map E.symm.toMonoidHom=symmetricEmbedding.range := by
    apply eq_symmetricEmbedding_range_of_index_two
    · rintro _ ⟨v,rfl⟩
      refine ⟨E (SemidirectProduct.inl v),hV ?_,E.symm_apply_apply _⟩
      rw [←hcore]
      exact mem_map_of_mem _ ⟨v,rfl⟩
    · exact (K.index_map_equiv E.symm).trans hindex
  have hm := congrArg (fun J : Subgroup S => J.map E.toMonoidHom) hK
  have he : E.toMonoidHom.comp E.symm.toMonoidHom = MonoidHom.id PE := by
    apply MonoidHom.ext
    intro x
    exact E.apply_symm_apply x
  rw [map_map,he,map_id,map_symmetricEmbedding_range E hcore] at hm
  exact hm

/-- Restricting the extended overlap to the ordinary plane gives the ordinary overlap. -/
theorem ordinary_overlap_image : ((overlap 1 hn).subgroupOf P).map j =
    ((Extension.overlap 1 hn).subgroupOf PE) ⊓ (j).range := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_,⟨x,rfl⟩⟩
    exact (Extension.binary_mem_overlap _).mpr hx
  · rintro ⟨hy,⟨x,rfl⟩⟩
    exact ⟨x,(Extension.binary_mem_overlap _).mp hy,rfl⟩
end CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane
