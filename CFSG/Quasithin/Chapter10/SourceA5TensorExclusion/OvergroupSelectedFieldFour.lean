module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupSelectedModels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFieldFour

/-!
# Field-four selection on the original tensor overgroup action

The four-model overgroup selector already uses the actual conjugation
quotient and the original B.5 moved section. Reconstructing its old proper
local A₅ image, with the same full Sylow marking, applies the field-size
refinement directly to that section. No further local or model hypothesis
is introduced. A corollary identifies the faithful component image with
one of the three concrete field-four carriers.

Source: Aschbacher–Smith 9.3.7, combined manuscript of 1 March 2004,
printed p.734, using A.3.14 and B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction ChapterA.Section03
open Representation Representation.BinaryOffender
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_overgroup_fourField_models
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
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype) C h.sectionData := by
  let := hr.normal
  let := hr.elementary
  let q := actionMk W
  let ρ := action W
  let N := offenderSubgroup ρ
  let C := (K.map q).subgroupOf N
  obtain ⟨hKN,heImage,h,hs⟩ := source_tensor_overgroup_four_models hH P K B L U W
    hK hKP hB hBK hLK eB hr hUW hBU hmoveB hmoveL hcomm hBOmega hm
  obtain ⟨hp,⟨eBI⟩,_,R,_,hlocal⟩ := source_tensor_overgroup_local_a5_image P K B L U W
    hK hB hBK hLK eB hUW hBU hmoveB hmoveL
  let i : K.map q ≃* C := (subgroupOfEquivOfLe hKN).symm
  let BI := (B.map q).subgroupOf (K.map q)
  let BI' := BI.map i.toMonoidHom
  let S := R.mapSurjective (q.subgroupMap_surjective K)
  let S' := S.mapSurjective (f := i.toMonoidHom) i.surjective
  obtain ⟨hp',⟨eBI'⟩,hlocal'⟩ := source_tensor_local_image_in_offender K W hKN S BI
    hlocal hp eBI
  exact ⟨hKN,heImage,h,SourceA5TensorExclusion.fourWayFourField_of_local_five
    (ρ.comp N.subtype) C h.sectionData hs S' BI' hlocal' hp'.ne eBI'⟩

theorem source_tensor_overgroup_field_four_actor_models
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
    letI := hr.normal
    Nonempty ((K.map (actionMk W)) ≃*
      SL(3,ChapterB.QuasisimpleSource.BinaryField.four.Carrier)) ∨
    Nonempty ((K.map (actionMk W)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) ∨
    Nonempty ((K.map (actionMk W)) ≃*
      Atlas.G2.Model ChapterB.QuasisimpleSource.BinaryField.four.Carrier) := by
  let := hr.normal
  let := hr.elementary
  obtain ⟨hKN,_,h,hs⟩ := source_tensor_overgroup_fourField_models hH P K B L U W
    hK hKP hB hBK hLK eB hr hUW hBU hmoveB hmoveL hcomm hBOmega hm
  let i := (subgroupOfEquivOfLe hKN).symm
  rcases hs.actor_models with ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨i.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨i.trans a⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨i.trans a⟩)

end CFSG.Quasithin.Chapter10
