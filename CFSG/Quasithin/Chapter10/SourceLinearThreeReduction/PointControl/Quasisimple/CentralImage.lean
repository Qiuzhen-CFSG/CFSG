module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation

/-!
# Noncentral core centers in the actual local images

The faithful-signalizer condition F*(L) = O₂(L) places Z(L) inside O₂(L).
Consequently a central image preserves the two-core quotient. The nonzero
fully moved subgroup survives in the center of the image's two-core and
cannot be central in the image. This uses no A₅ marking or irreducibility.

Source: Aschbacher--Smith 10.2.9, printed pp.750--751. The literal marked
application supplies the G₂, triality and J₁ point-component comparisons.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- Every central image of the original faithful local component has a
noncentral two-core center. Full movement prevents the image of the moved
module from becoming central or trivial. -/
theorem central_image_core_center_not_central
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) : ¬ (center (pCore 2 H)).map (pCore 2 H).subtype ≤ center H := by
  let W := ⁅D.fullModule,L⁆
  let A := W.subgroupOf L
  have hWL : W ≤ L := source_full_moved_le_component D
  have hmapA : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hA : A.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let := hA
  let := source_original_full_moved_elementary D
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmapA,←MonoidHom.range_eq_map,range_subtype]
    exact source_full_moved_eq_commutator D
  have hAne : A ≠ ⊥ := by
    intro h
    have hh := congrArg (map L.subtype) h
    rw [hmapA,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D hh
  have hz : center L ≤ pCore 2 L := by
    rw [←D.faithful.1.2.2]
    exact (show center L ≤ fittingSubgroup L from
      le_sSup ⟨inferInstance, inferInstance⟩).trans (fitting_le_generalizedFitting L)
  have hkp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hker.trans hz)
  have hcore : (pCore 2 L).map f = pCore 2 H := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hkp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let N := A.map f
  let : N.Normal := hA.map f hf
  have hNp : IsPGroup 2 N := hAp.map f
  have hNcore : N ≤ pCore 2 H := le_sSup ⟨inferInstance,hNp⟩
  have hNc : N ≤ centralizer (pCore 2 H : Set H) := by
    rintro _ ⟨w,hw,rfl⟩ q hq
    rw [←hcore] at hq
    obtain ⟨r,hr,rfl⟩ := hq
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    have hh : w*r=r*w := Subtype.ext
      (source_component_core_centralizes_fullModule D (mem_map_of_mem L.subtype hr)
        w (hWV hw))
    simpa only [map_mul] using congrArg f hh.symm
  have hNmove : ⁅N,(⊤ : Subgroup H)⁆ = N := by
    rw [show (⊤ : Subgroup H) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  have hNnoncentral : ¬ N ≤ center H := by
    intro hn
    have hNzero : N = ⊥ := hNmove.symm.trans
      (commutator_top_right_eq_bot_iff_le_center.mpr hn)
    have hak : A ≤ f.ker := (map_eq_bot_iff A).mp hNzero
    have haz : A ≤ center L := hak.trans hker
    exact hAne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr haz))
  intro hc
  apply hNnoncentral
  intro n hn
  exact hc ⟨⟨n,hNcore hn⟩,
    mem_center_iff.mpr (fun r => Subtype.ext (hNc hn r r.property)),rfl⟩

/-- The literal local image in any marked containing central quotient has
noncentral two-core center. -/
theorem marked_core_center_not_central
    {I : Subgroup G} (hLI : L ≤ I) {H : Type*} [Group H] [Finite H]
    (eI : (I ⧸ center I) ≃* H) :
    let B := (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    ¬ (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  let A := L.subgroupOf I
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change eI (QuotientGroup.mk' (center I) (inclusion hLI l)) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp
      (eI.injective (hh.trans (map_one eI).symm))
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  exact central_image_core_center_not_central D f hf hk

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
