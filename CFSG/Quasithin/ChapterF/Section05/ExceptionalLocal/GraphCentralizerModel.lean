module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerSource
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionMarkedCentralizer
public import Theory.SpecificGroups.DihedralProduct.CentralFactorQuotient
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowCentralizerNonfusion
public import Theory.ElementaryAbelian.Injective
/-!
# The marked graph-centralizer Sylow quotient

The graph involution is the central involution of the first dihedral factor.
Its quotient is therefore E4 × D8. The root lift maps to the unique nontrivial
derived element; its centralizer is the Sylow subgroup, which consequently
normalizes only itself. Sylow fusion then separates its central involutions.

This proves the first paragraph of Aschbacher--Smith F.5.5, printed p.301,
including the center of order eight needed by the two transfer steps on p.302.
All conclusions use the original source hypotheses and the literal quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_graph_R_marked_iso (R : Sylow 2 (C c i)) :
    ∃ e : R ≃* DihedralGroup 4 × DihedralGroup 4,
      ∀ x:R, ((x:C c i):G)=Source.graphElement c i → e x=(DihedralGroup.r 2,1) := by
  obtain ⟨g,hg,hmap⟩ := exists_graph_short_sylow_conjugator c i z
    (sourceMarkedShort c i) (source_fusionFacts c i z h) R
  obtain ⟨d,hd,_⟩ := source_short_Tcentralizer_marked_iso c i z h
  let a := (R : Subgroup (C c i)).equivMapOfInjective (C c i).subtype (C c i).subtype_injective
  let b := ((MulAut.conj g).subgroupMap (Rimage c i R)).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨a.trans (b.trans d),?_⟩
  intro x hx
  apply hd
  change MulAut.conj g ((x:C c i):G)=sourceMarkedShort c i
  rw [hx]
  exact hg

open DihedralProductCentralFactorQuotient in
 theorem source_graph_quotient_marked_model (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    ∃ eR : R≃*(DihedralGroup 4 × DihedralGroup 4),
      ∃ e : ((R:Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))) ≃* (DihedralProductCentralFactorQuotient.E4 × DihedralGroup 4),
      ∀ x:R, e ⟨QuotientGroup.mk' (zpowers (graphInCentralizer c i)) x.val,
        mem_map_of_mem _ x.property⟩=modelMap (eR x) := by
  obtain ⟨eR,heR⟩ := source_graph_R_marked_iso c i z h R
  let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  have hfR : graphInCentralizer c i ∈ (R:Subgroup (C c i)) := by
    apply (mem_map_iff_mem (C c i).subtype_injective).mp
    exact normalizer_A_le_Rimage c i z (sourceMarkedShort c i) (source_fusionFacts c i z h)
      R hR false (source_graph_mem_A c i h.embedding_injective false)
  let fR : R := ⟨graphInCentralizer c i,hfR⟩
  let k : (DihedralGroup 4 × DihedralGroup 4) →* C c i := (R:Subgroup (C c i)).subtype.comp eR.symm.toMonoidHom
  have hk : Function.Injective k := (R:Subgroup (C c i)).subtype_injective.comp eR.symm.injective
  have hkf : k (DihedralGroup.r 2,1)=graphInCentralizer c i := by
    have he : eR fR=(DihedralGroup.r 2,1) := heR fR rfl
    have hh := eR.symm_apply_apply fR
    rw [he] at hh
    exact congrArg (fun x:R => (x:C c i)) hh
  let j := q.comp k
  have hker (x:(DihedralGroup 4 × DihedralGroup 4)) : j x=1 ↔ x=1 ∨ x=(DihedralGroup.r 2,1) := by
    change q (k x)=1 ↔ _
    rw [graph_quotient_eq_one_iff c i z h]
    constructor
    · rintro (hx|hx)
      · exact Or.inl (hk (hx.trans k.map_one.symm))
      · exact Or.inr (hk (hx.trans hkf.symm))
    · rintro (rfl|rfl)
      · exact Or.inl k.map_one
      · exact Or.inr hkf
  obtain ⟨e0,he0⟩ := exists_range_equiv j hker
  have hkR : k.range=(R:Subgroup (C c i)) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (eR.symm y).property
    · intro hx
      exact ⟨eR ⟨x,hx⟩,by simp [k]⟩
  have hjR : j.range=(R:Subgroup (C c i)).map q := by
    rw [MonoidHom.range_comp,hkR]
  let e := (MulEquiv.subgroupCongr hjR).symm.trans e0
  refine ⟨eR,e,?_⟩
  intro x
  have hx : (MulEquiv.subgroupCongr hjR).symm ⟨q x.val,mem_map_of_mem q x.property⟩=
      ⟨j (eR x),⟨eR x,rfl⟩⟩ := by
    apply Subtype.ext
    change q x.val=j (eR x)
    simp [j,k]
  change e0 ((MulEquiv.subgroupCongr hjR).symm _) = _
  rw [hx]
  exact he0 (eR x)

open DihedralProductCentralFactorQuotient in
theorem source_graph_quotient_derived_centralizer (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
    let S := (R:Subgroup (C c i)).map q
    ∃ u:C c i, orderOf (q u)=2 ∧ centralizer ({q u}:Set (graphCentralQuotient c i))=S ∧
      ⁅S,S⁆=zpowers (q u) := by
  intro q S
  obtain ⟨u,hu,hzu,hfu,hC,ho,hqC⟩ := exists_graph_quotient_sylow_centralizer_with_lift
    c i z (sourceMarkedShort c i) (source_fusionFacts c i z h) h R
    (source_normalizer_joint_centralizer c i z h)
  obtain ⟨eR,e,he⟩ := source_graph_quotient_marked_model c i z h R hR
  let uR:R := ⟨u,hu⟩
  have huZ : uR∈center R := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    apply Subtype.ext
    have ha : ((a:C c i):G)∈Rimage c i R := mem_map_of_mem _ a.property
    rw [←hC] at ha
    exact mem_centralizer_singleton_iff.mp ha.2
  have heZ : eR uR∈center (DihedralGroup 4 × DihedralGroup 4) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨b,rfl⟩ := eR.surjective a
    simpa only [map_mul] using congrArg eR (mem_center_iff.mp huZ b)
  let uS:S := ⟨q u,mem_map_of_mem q hu⟩
  have heu : e uS=(1,DihedralGroup.r 2) := by
    have hh := he uR
    change e uS=modelMap (eR uR) at hh
    rcases modelMap_center_cases (eR uR) heZ with hz|hz
    · have hu1 : uS=1 := e.injective ((hh.trans hz).trans e.map_one.symm)
      have hq1 : q u=1 := congrArg Subtype.val hu1
      rw [hq1,orderOf_one] at ho
      omega
    · exact hh.trans hz
  have hd : _root_.commutator S=zpowers uS := by
    apply map_injective (f:=e.toMonoidHom) e.injective
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,MonoidHom.map_zpowers]
    change ⁅(⊤:Subgroup (DihedralProductCentralFactorQuotient.E4 × DihedralGroup 4)),⊤⁆=zpowers (e uS)
    rw [heu]
    exact model_commutator
  refine ⟨u,ho,hqC,?_⟩
  rw [←S.map_subtype_commutator,hd,MonoidHom.map_zpowers]
  rfl

theorem source_graph_quotient_normalizer (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    let S := (R:Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
    normalizer (S:Set (graphCentralQuotient c i))=S := by
  intro S
  obtain ⟨u,ho,hc,hd⟩ := source_graph_quotient_derived_centralizer c i z h R hR
  apply le_antisymm ?_ S.le_normalizer
  exact (normalizer_le_centralizer_of_characteristic_involution S (_root_.commutator S)
    _ ho (S.map_subtype_commutator.trans hd)).trans hc.le

theorem source_graph_quotient_center_nonfusion (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    let S := (R:Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
    ∀ x y:graphCentralQuotient c i, x∈centralizer (S:Set (graphCentralQuotient c i)) →
      y∈centralizer (S:Set (graphCentralQuotient c i)) → IsConj x y → x=y := by
  intro S x y hx hy hxy
  let P := R.mapSurjective (f:=QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
    (QuotientGroup.mk'_surjective _)
  apply Eq.symm
  apply P.eq_of_isConj_of_normalizer_le_centralizer x y hx hy ?_ hxy
  rw [show normalizer (P:Set (graphCentralQuotient c i))=S from
    source_graph_quotient_normalizer c i z h R hR]
  intro a ha
  exact mem_centralizer_singleton_iff.mpr (hx a ha)


theorem source_graph_quotient_sylow_card (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    Nat.card ((R:Subgroup (C c i)).map
      (QuotientGroup.mk' (zpowers (graphInCentralizer c i))))=32 := by
  obtain ⟨eR,e,he⟩ := source_graph_quotient_marked_model c i z h R hR
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem source_graph_quotient_center_card (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    Nat.card (center ((R:Subgroup (C c i)).map
      (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))))=8 := by
  obtain ⟨eR,e,he⟩ := source_graph_quotient_marked_model c i z h R hR
  exact (Nat.card_congr (centerCongr e).toEquiv).trans
    DihedralProductCentralFactorQuotient.model_center_card

theorem source_graph_quotient_center_elementary (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R:Subgroup (C c i))) :
    IsElementaryAbelian 2 (center ((R:Subgroup (C c i)).map
      (QuotientGroup.mk' (zpowers (graphInCentralizer c i))))) := by
  obtain ⟨eR,e,he⟩ := source_graph_quotient_marked_model c i z h R hR
  let := DihedralProductCentralFactorQuotient.model_center_elementary
  exact IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom (centerCongr e).injective

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
