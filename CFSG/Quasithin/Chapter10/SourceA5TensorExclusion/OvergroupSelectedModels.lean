module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OffenderLocalImage
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.SieveCohomology
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupA7

/-!
# Model selection for the original tensor overgroup action

The old component's proper local A₅ image restricts the full B.5 action
classification to six literal models. The actual Sylow omega center is fixed
by the old component; once the orbit is fully moved, both A₇ models are
excluded, leaving the linear, repeated linear, symplectic and G₂ actions.
The quotient action, offender actor and Sylow maps remain the original ones.

Source: Aschbacher–Smith 9.3.7, printed p.734, using B.5.1 and A.3.14.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction ChapterA.Section03
open Representation Representation.BinaryOffender
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_overgroup_six_models
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (P : Sylow 2 H)
    (K B L U W : Subgroup H) [K.Normal]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hB : B ∈ localCComponents P) (hBK : B ≤ K) (hLK : L ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hr : IsPReduced 2 W) (hUW : U ≤ W)
    (hBU : B ≤ centralizer (U : Set H))
    (hmoveB : ¬ B ≤ centralizer (componentOrbit U L : Set H))
    (hmoveL : ¬ L ≤ centralizer (U : Set H))
    (hcomm : B = ⁅B,elementaryAbelianMaxJ (P : Subgroup H)⁆) :
    letI := hr.normal; letI := hr.elementary
    let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
    let N := offenderSubgroup ρ
    let C := (K.map (actionMk W)).subgroupOf N
    K.map (actionMk W) ≤ N ∧
    Nonempty ((B.map (actionMk W) ⧸ pCore 2 (B.map (actionMk W))) ≃* alternatingGroup (Fin 5)) ∧
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) C,
      SourceA5PointFFModels.SixWayWithIrreducible (ρ.comp N.subtype) C h.sectionData := by
  let := hr.normal
  let := hr.elementary
  let q := actionMk W
  let ρ := action W
  let N := offenderSubgroup ρ
  let C := (K.map q).subgroupOf N
  have hBW : componentOrbit U L ≤ W :=
    iSup_conjugates_le_of_le_normalizer U L W hUW le_normalizer_of_normal
  have hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) :=
    ChapterC.MSCentralOrbit.thompson_moves_of_component_commutator (P : Subgroup H) B W hcomm
      (fun hc => hmoveB (hc.trans (centralizer_le hBW)))
  let : IsQuasisimple (K.map q) := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple hH P K W hK hKP
      hr.quotient_pCore_eq_bot hmove
  have hKN : K.map q ≤ N := component_le_offenderSubgroup P K W hKP
    hr.quotient_pCore_eq_bot hmove
  let i : K.map q ≃* C := (subgroupOfEquivOfLe hKN).symm
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv i
  obtain ⟨hp,⟨eBI⟩,hker,R,hR,hlocal⟩ := source_tensor_overgroup_local_a5_image P K B L U W
    hK hB hBK hLK eB hUW hBU hmoveB hmoveL
  let BI := (B.map q).subgroupOf (K.map q)
  let BI' := BI.map i.toMonoidHom
  let S := R.mapSurjective (q.subgroupMap_surjective K)
  let S' := S.mapSurjective (f := i.toMonoidHom) i.surjective
  obtain ⟨hp',⟨eBI'⟩,hlocal'⟩ := source_tensor_local_image_in_offender K W hKN S BI
    hlocal hp eBI
  let bImage : B.map q ≃* BI := (subgroupOfEquivOfLe (map_mono hBK)).symm
  let eImage : (B.map q ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ bImage (pCore_map_iso 2 bImage)).trans eBI
  obtain ⟨h⟩ := quasisimple_source_conclusion_of_thompson_movement hH P K W hK hKP
    hr.quotient_pCore_eq_bot hmove
  exact ⟨hKN,⟨eImage⟩,h,SourceA5PointFFModels.sixWayWithIrreducible_of_source (ρ.comp N.subtype) C h
    S' BI' hlocal' hp'.ne eBI'⟩
theorem source_tensor_overgroup_four_models
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (P : Sylow 2 H)
    (K B L U W : Subgroup H) [K.Normal]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hB : B ∈ localCComponents P) (hBK : B ≤ K) (hLK : L ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hr : IsPReduced 2 W) (hUW : U ≤ W)
    (hBU : B ≤ centralizer (U : Set H))
    (hmoveB : ¬ B ≤ centralizer (componentOrbit U L : Set H))
    (hmoveL : ¬ L ≤ centralizer (U : Set H))
    (hcomm : B = ⁅B,elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hBOmega : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (hm : letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype) ((K.map (actionMk W)).subgroupOf N) = ⊤) :
    letI := hr.normal; letI := hr.elementary
    let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
    let N := offenderSubgroup ρ
    let C := (K.map (actionMk W)).subgroupOf N
    K.map (actionMk W) ≤ N ∧
    Nonempty ((B.map (actionMk W) ⧸ pCore 2 (B.map (actionMk W))) ≃* alternatingGroup (Fin 5)) ∧
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) C,
      SourceA5TensorExclusion.FourWay (ρ.comp N.subtype) C h.sectionData := by
  let := hr.normal
  let := hr.elementary
  obtain ⟨hKN,⟨eImage⟩,h,hs⟩ := source_tensor_overgroup_six_models hH P K B L U W
    hK hKP hB hBK hLK eB hr hUW hBU hmoveB hmoveL hcomm
  exact ⟨hKN,⟨eImage⟩,h,source_tensor_fourWay_of_sixWay W P K B hBOmega eImage hKN
    h.sectionData hm hs⟩

end CFSG.Quasithin.Chapter10
