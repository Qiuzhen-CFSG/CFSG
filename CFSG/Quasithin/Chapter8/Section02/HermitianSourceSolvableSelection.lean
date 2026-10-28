module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCenter
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Witness
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Actual solvable family selection for the Hermitian source

The proved solvable E.2.9 witness is transported from H to the ambient
subgroup lattice. The same inclusion transports its internal conjugator,
Sylow intersection, normal core and dihedral quotient; the source right
conjugator is the inverse of the witness's left conjugator. Parameter one
divides the original generation parameter without a model-degree premise.

For an already marked rank-one family, the core, center and non-FF
intersection calculations select the pair without positive weak closure.
This gives the actual selected pair in every solvable E.2.8 group, including
the field-four case. The Chapter 12 extension applies it to the original
chosen orbit and tensor. Nonsolvable family existence and the field-four
normalizer/centralizer exclusion remain with the source assembly.

The internal Chapter B import only unfolds the original maximal normal
core for the comparison; its public boundary is unchanged.
Source: Aschbacher–Smith E.2.9 and 8.2.2, printed pp.221–222,714–715
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

private theorem map_pair {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (W : Subgroup X) (x : X) :
    (W ⊔ W.map (MulAut.conj x).toMonoidHom).map f =
      W.map f ⊔ (W.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext y
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

private theorem family_of_dihedral_witness
    {H T M V : Subgroup G} (hVH : V ≤ H)
    (hV : IsElementaryAbelian 2 V) (hne : V ≠ ⊥) (hVT : V ≤ T)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    (w : Witnesses.Solvable.Witness R (M.subgroupOf H) (V.subgroupOf H)) :
    ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 := by
  let J := w.subgroup
  let I := J.map H.subtype
  let e : J ≃* I := J.equivMapOfInjective H.subtype H.subtype_injective
  let A := (M.subgroupOf H).subgroupOf J
  have hA : (M.subgroupOf I).comap e.toMonoidHom = A := by ext x; rfl
  have hC : (localCore M I).comap e.toMonoidHom = A.normalCore := by
    rw [←normalCore_comap_of_surjective e.toMonoidHom e.surjective,hA]
  have hCm : A.normalCore.map e.toMonoidHom = localCore M I := by
    rw [←hC,map_comap_eq,MonoidHom.range_eq_top.mpr e.surjective,top_inf_eq]
  let ec : A.normalCore ≃* localCore M I :=
    (e.subgroupMap A.normalCore).trans (MulEquiv.subgroupCongr hCm)
  have hclosed : IsTwoClosed (localCore M I) := by
    obtain ⟨P,hP⟩ := w.core_two_closed
    let := hP
    refine ⟨P.mapSurjective (f := ec.toMonoidHom) ec.surjective,?_⟩
    exact Normal.map hP ec.toMonoidHom ec.surjective
  let eqt : (J ⧸ A.normalCore) ≃* Star M I :=
    QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective _ _ hC
  have hr : RankOneAlternative (Star M I) (starImage M I M) 1 := by
    obtain ⟨p,a,hp,hp2,ha,⟨d⟩⟩ := w.dihedral
    exact Or.inr (Or.inr ⟨rfl,p,a,hp,hp.odd_of_ne_two hp2,ha,⟨eqt.symm.trans d⟩⟩)
  have hgen : V ⊔ V.map (MulAut.conj (w.conjugator.val.val)).toMonoidHom = I := by
    have hh := congrArg (fun B : Subgroup J => B.map (H.subtype.comp J.subtype)) w.generate
    rw [map_pair] at hh
    have hm : ((V.subgroupOf H).subgroupOf J).map (H.subtype.comp J.subtype) = V := by
      rw [←map_map,map_subgroupOf_eq_of_le w.le,map_subgroupOf_eq_of_le hVH]
    rw [hm,←MonoidHom.range_eq_map,MonoidHom.range_comp,J.range_subtype] at hh
    exact hh
  let S := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup I) = T.subgroupOf I := by
    apply map_injective I.subtype_injective
    change ((w.sylow : Subgroup J).map e.toMonoidHom).map I.subtype = _
    rw [map_map]
    have hf : I.subtype.comp e.toMonoidHom = H.subtype.comp J.subtype := rfl
    rw [hf,←map_map,w.sylow_eq,hR,map_inf _ _ _ H.subtype_injective,
      subgroupOf_map_subtype,subgroupOf_map_subtype]
    change (T ⊓ H) ⊓ I = T ⊓ I
    rw [inf_assoc,inf_eq_right.mpr (map_subtype_le J)]
  refine ⟨I,⟨hV,hne,hVT,map_subtype_le J,?_,⟨S,hS⟩,hclosed,Or.inl hr,one_dvd _⟩,hr⟩
  refine ⟨w.conjugator.val.val⁻¹,?_,?_⟩
  · exact I.inv_mem (mem_map_of_mem H.subtype w.conjugator.property)
  · simpa only [inv_inv] using hgen

/-- The actual solvable E.2.8 input supplies a parameter-one family member. -/
theorem exists_dihedral_family_of_solvable
    {K : GroupClass} {H T M V : Subgroup G}
    (h : HypothesisE28 K H T M V) (hsol : Group.IsSolvable H) :
    ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 := by
  let := h.elementary
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  have hVR : V.subgroupOf H ≤ R := by rw [hR]; exact comap_mono h.le_sylow
  have hnorm : ((V.subgroupOf H).subgroupOf (R : Subgroup H)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hVR).mpr
    rw [hR,←subgroupOf_normalizer_eq hVH]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow)
  have hcore : V.subgroupOf H ≤ (ChapterB.minimalParabolicMax R hP).pCoreIn 2 := by
    rw [←hM]
    intro v hv
    obtain ⟨x,hx,he⟩ := h.le_local_core hv
    exact ⟨x,hx,Subtype.ext he⟩
  have hout : ¬ V.subgroupOf H ≤ ChapterB.minimalParabolicCore R hP := by
    intro hc
    apply h.outside_core
    have hh := map_mono (f := H.subtype) hc
    rw [map_subgroupOf_eq_of_le hVH] at hh
    simpa only [ChapterB.minimalParabolicCore,←hM] using hh
  obtain ⟨w⟩ := Witnesses.Solvable.solvable_witness R hP hsol (V.subgroupOf H)
    hVR hnorm hcore hout
  rw [←hM] at w
  have hne : V ≠ ⊥ := by intro he; exact h.outside_core (he ▸ bot_le)
  exact family_of_dihedral_witness hVH h.elementary hne h.le_sylow R hR w

/-- A marked rank-one family can be selected without a weak-closure premise. -/
theorem exists_selected_of_rank_one_family
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ := family_intersection_ne_bot_of_quadraticRatio_gt_one h hchar f i hgen hqH
  have hc := family_rank_one_core h f hr
  have hmodel := hr.map (coreQuotientEquiv M I hc)
  rw [starImage_map_coreQuotientEquiv] at hmodel
  have hz := family_rank_one_center h hchar f hr i hgen hTI hNV hZ
  obtain ⟨hzcore,hncore⟩ := core_markings_of_star M I T V hc hz
    (family_borel_normalizes h f hr i hgen hTI hNV hZ)
  have hTM : T ≤ M := by
    obtain ⟨R,hR,hP,hM⟩ := h.minimal
    intro t ht
    have htm := (ChapterB.minimalParabolicMax_spec R hP).2
    rw [hR,←hM] at htm
    exact htm (show (⟨t,h.le_ambient ht⟩ : H) ∈ T.subgroupOf H from ht)
  obtain ⟨hnorm,hrank⟩ := selected_model_markings selectionModelSources M I T V k S hS hTM hmodel hzcore hncore
  refine ⟨i,S,f,hgen,hS,Family.twoConjugate h f S hS i hgen,hc,
    family_characteristic_two h f hchar,hZ,?_,hNI,?_,hr.models.1,f.parameter_dvd,
    hmodel,hzcore,hnorm,hrank,selected_quadraticRatio_gt_one M I V hNI hq⟩
  · exact intersection_central I V i.val hgen
  · exact relative_normalizer I M V i.val hgen hTI hNV hZ

/-- Solvable E.2.8 groups supply the actual selected parameter-one pair,
including when positive weak closure has not yet been established. -/
theorem exists_selected_of_solvable
    {K : GroupClass} {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hsol : Group.IsSolvable H)
    (hchar : generalizedFitting H = pCore 2 H)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I), Selected H T M V I 1 i S := by
  obtain ⟨I,f,hr⟩ := exists_dihedral_family_of_solvable h hsol
  obtain ⟨i,S,s⟩ := exists_selected_of_rank_one_family h hchar f hr hq hTI hNV
  exact ⟨I,i,S,s⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
