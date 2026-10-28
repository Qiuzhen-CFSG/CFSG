module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFPreparation
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFSelection
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFA7
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFieldFour
/-!
# The original nonzero-core line action

For the original overgroup X = H ∨ A, the old perfect residual lies in
both a normal C-component J and the offender actor on the reduced Omega
orbit W. A proper normal subgroup of a C-component is solvable, so the
whole image of J belongs to that actor. The complete adequate actor
classification then makes this image quasisimple. Its proper local A₅
subgroup selects the original six FF models.

The actual moved section excludes both alternating-seven models without
requiring all of W to be moved. The same local A₅ marking forces field
size four in the remaining linear, symplectic and G₂ rows. The Cartan
factor A remains in the equality X = J T A throughout. The subsequent
Lie-type Cartan normalization is a separate source step.

Source: Aschbacher--Smith, Proposition 9.3.1, printed pp.732--733,
using A.3.14 and B.5.6.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open Subgroup Theory.GroupTheory Stellmacher
open ChapterB.InternalThompsonAction ChapterC.MSCentralOrbit ChapterA.Section03
open Representation Representation.BinaryOffender
variable {X : Type*} [Group X] [Finite X]

private theorem cComponent_le_normal_of_perfect_intersection
    (J K N : Subgroup X) [N.Normal] [Group.IsPerfect K]
    (hJ : J.IsCComponent) (hK : K ≠ ⊥) (hKJ : K ≤ J) (hKN : K ≤ N) : J ≤ N := by
  by_contra hJN
  have hp : N.subgroupOf J ≠ ⊤ := fun he => hJN (subgroupOf_eq_top.mp he)
  let : Group.IsSolvable (N.subgroupOf J) :=
    hJ.isSolvable_of_subnormal_lt_top (inferInstance : (N.subgroupOf J).Normal).isSubnormal hp
  let f : K →* N.subgroupOf J := (inclusion hKJ).codRestrict _ (by
    intro k
    exact hKN k.property)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun n : N.subgroupOf J => ((n : J) : X)) hab)
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hf
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- A perfect moving subgroup in the offender actor brings its entire normal
C-component into that actor. The corrected adequate classification then gives
quasisimplicity without a Sylow-generation hypothesis. -/
theorem quasisimple_image_of_perfect_offender_subgroup
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (J K W : Subgroup X) [J.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    [Group.IsPerfect K] (hJ : J.IsCComponent) (hKJ : K ≤ J)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hKne : K.map (actionMk W) ≠ ⊥)
    (hKN : K.map (actionMk W) ≤ offenderSubgroup (action W)) :
    J.map (actionMk W) ≤ offenderSubgroup (action W) ∧
      IsQuasisimple (J.map (actionMk W)) := by
  let q := actionMk W
  let I := J.map q
  let N := offenderSubgroup (action W)
  let : I.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  let : N.Normal := offenderSubgroup_normal _
  let : Group.IsPerfect (K.map q) := Group.IsPerfect.map q
  have hIne : I ≠ ⊥ := fun he => hKne (bot_unique ((map_mono hKJ).trans_eq he))
  have hI : I.IsCComponent :=
    (NonquasisimpleAction.ccomponent_image_or_bot hJ q (QuotientGroup.mk'_surjective _)).resolve_left hIne
  have hIN : I ≤ N := cComponent_le_normal_of_perfect_intersection I (K.map q) N
    hI hKne (map_mono hKJ) hKN
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (ActionQuotient W) :=
    { Cover := X
      kernel := centralizer (W : Set X)
      sqtk := hX
      equiv := MulEquiv.refl _ }
  have hclass := ChapterB.SourceInduction.offenderSubgroup_adequateAlternative
    (action W) (action_faithful W) hcore c
  let : IsQuasisimple (I.subgroupOf N) := SourceOldResidual.cComponent_quasisimple_of_adequate
    (ρ := (action W).comp N.subtype) hclass (hI.subgroupOf hIN)
  exact ⟨hIN,IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hIN)⟩

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Stellmacher
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual normal overcomponent has quasisimple image on the original
Omega orbit. The odd Cartan extension remains in the ambient actor. -/
theorem nonzero_core_cartan_quasisimple_image
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥)
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    let X : Subgroup G := H ⊔ A
    let P := T.subtype ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans
      (show H ≤ X from le_sup_left))
    let K := ((pResidual 2 H).map H.subtype).subgroupOf X
    let W := omegaOrbit (P : Subgroup X)
    ∃ J : Subgroup X, J.IsCComponent ∧ J.Normal ∧ K ≤ J ∧
      (J ⊔ (P : Subgroup X)) ⊔ A.subgroupOf X = ⊤ ∧
      ∃ hr : IsPReduced 2 W,
        letI := hr.normal; letI := hr.elementary
        m.tensorLine.subgroupOf X ≤ W ∧ IsFFModule (V := Additive W) (action W) ∧
        J.map (actionMk W) ≤ offenderSubgroup (action W) ∧
        IsQuasisimple (J.map (actionMk W)) ∧
        let q := actionMk W
        let KI := (K.map q).subgroupOf (J.map q)
        KI < ⊤ ∧ Nonempty ((KI ⧸ pCore 2 KI) ≃* alternatingGroup (Fin 5)) ∧
          Group.IsSolvable (q.subgroupMap J).ker ∧
          ∃ R : Sylow 2 J, (R : Subgroup J) = (P : Subgroup X).subgroupOf J ∧
            KI ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective J)) := by
  dsimp only
  let X : Subgroup G := H ⊔ A
  let K0 := (pResidual 2 H).map H.subtype
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left
  have hKX : K0 ≤ X := (map_subtype_le _).trans le_sup_left
  have hUX : m.tensorLine ≤ X := m.tensorLine_le_sylow.trans hTX
  let P := T.subtype hTX
  let W := omegaOrbit (P : Subgroup X)
  let K := K0.subgroupOf X
  obtain ⟨_,hs,J,hJ,hnJ,hKJ,hgen,hr,hUW,hFF,hKN,hproper⟩ :=
    m.nonzero_core_cartan_original_data hH eK A B hAB hA9 hAe hB3 hBC hcore hmove
  let := hnJ
  let := hr.normal
  let := hr.elementary
  let : Group.IsPerfect K0 := Chapter1.mem_L_isPerfect (source_hstar_residual_mem_local_of_a5 hH eK)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKX).symm.toMonoidHom) (subgroupOfEquivOfLe hKX).symm.surjective
  have hKne : K.map (actionMk W) ≠ ⊥ := by
    intro hz
    have hKW : K ≤ centralizer (W : Set X) := by
      simpa only [actionMk,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff K).mp hz
    apply hmove
    intro k hk u hu
    exact congrArg Subtype.val (hKW (show (⟨k,hKX hk⟩ : X) ∈ K from hk)
      ⟨u,hUX hu⟩ (hUW hu))
  obtain ⟨hJN,hq⟩ := SourceOldResidualLineFF.quasisimple_image_of_perfect_offender_subgroup
    hs J K W hJ hKJ hr.quotient_pCore_eq_bot hKne hKN
  exact ⟨J,hJ,hnJ,hKJ,hgen,hr,hUW,hFF,hJN,hq,hproper⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Stellmacher
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original nonzero-core 9.3.1 action satisfies the six-model selector
and its four-field refinement on the same moved section. Both the original
odd Cartan factor and the literal source action are retained. -/
theorem nonzero_core_cartan_six_models
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥)
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    let X : Subgroup G := H ⊔ A
    let P := T.subtype ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans
      (show H ≤ X from le_sup_left))
    let K := ((pResidual 2 H).map H.subtype).subgroupOf X
    let W := omegaOrbit (P : Subgroup X)
    ∃ J : Subgroup X, J.IsCComponent ∧ J.Normal ∧ K ≤ J ∧
      (J ⊔ (P : Subgroup X)) ⊔ A.subgroupOf X = ⊤ ∧
      ∃ hr : IsPReduced 2 W,
        letI := hr.normal; letI := hr.elementary
        let ρ := action W
        let N := offenderSubgroup ρ
        let C := (J.map (actionMk W)).subgroupOf N
        m.tensorLine.subgroupOf X ≤ W ∧ IsFFModule (V := Additive W) ρ ∧
        J.map (actionMk W) ≤ N ∧ IsQuasisimple (J.map (actionMk W)) ∧
        C = generalizedFitting N ∧
        ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) C,
          SourceA5PointFFModels.SixWayWithIrreducible (ρ.comp N.subtype) C h.sectionData ∧
          SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype) C h.sectionData := by
  dsimp only
  let X : Subgroup G := H ⊔ A
  let K0 := (pResidual 2 H).map H.subtype
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left
  let P := T.subtype hTX
  let W := omegaOrbit (P : Subgroup X)
  let K := K0.subgroupOf X
  obtain ⟨J,hJ,hnJ,hKJ,hgen,hr,hUW,hFF,hJN,hq,hp,⟨eKI⟩,hker,R,hR,hlocal⟩ :=
    m.nonzero_core_cartan_quasisimple_image hH eK A B hAB hA9 hAe hB3 hBC hcore hmove
  let := hnJ
  let := hr.normal
  let := hr.elementary
  let q := actionMk W
  let I := J.map q
  let N := offenderSubgroup (action W)
  let C := I.subgroupOf N
  let KI := (K.map q).subgroupOf I
  let S := R.mapSurjective (q.subgroupMap_surjective J)
  let i : I ≃* C := (subgroupOfEquivOfLe hJN).symm
  let S' := S.mapSurjective (f := i.toMonoidHom) i.surjective
  let KI' := KI.map i.toMonoidHom
  obtain ⟨hp',⟨eKI'⟩,hlocal'⟩ := source_tensor_local_image_in_offender J W hJN S KI hlocal hp eKI
  let : I.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple I := hq
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv i
  have hC : C.IsCComponent :=
    (show IsComponent N C from ⟨(inferInstance : C.Normal).isSubnormal,inferInstance⟩).isCComponent
  have hXH : X ∈ Chapter1.H G := by
    intro hb
    exact hcore ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (ActionQuotient W) :=
    { Cover := X
      kernel := centralizer (W : Set X)
      sqtk := Chapter3.sqtk_of_mem_H D.simpleQTKE hXH
      equiv := MulEquiv.refl _ }
  have hclass := ChapterB.SourceInduction.offenderSubgroup_adequateAlternative
    (action W) (action_faithful W) hr.quotient_pCore_eq_bot c
  obtain ⟨hfit,⟨h⟩⟩ := SourceOldResidual.quasisimple_source_of_adequate_of_proper_local_five
    hclass hC S' KI' hlocal' hp'.ne eKI'
  have hsix := SourceA5PointFFModels.sixWayWithIrreducible_of_source
    ((action W).comp N.subtype) C h S' KI' hlocal' hp'.ne eKI'
  let bImage : K.map q ≃* KI := (subgroupOfEquivOfLe (map_mono hKJ)).symm
  let eImage : ((K.map q) ⧸ pCore 2 (K.map q)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ bImage (pCore_map_iso 2 bImage)).trans eKI
  have hKOmega : K ≤ centralizer (omegaCenterIn (P : Subgroup X) : Set X) := by
    intro k hk z hz
    have hz' := (mem_omegaCenterIn_iff _ _).mp hz
    have hzG : (z : G) ∈ omegaCenterIn (T : Subgroup G) := by
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨hz'.1,?_,congrArg Subtype.val hz'.2.2⟩
      intro t ht
      exact congrArg Subtype.val (hz'.2.1 ⟨t,hTX ht⟩ ht)
    exact Subtype.ext (m.old_residual_centralizes_sylowOmega hH hk z hzG)
  have hfour := SourceOldResidualLineFF.fourWay_of_sixWay
    W P J K hKJ hKOmega eImage hJN h.sectionData hsix
  exact ⟨J,hJ,hnJ,hKJ,hgen,hr,hUW,hFF,hJN,hq,hfit,h,hsix,
    SourceA5TensorExclusion.fourWayFourField_of_local_five
      ((action W).comp N.subtype) C h.sectionData hfour S' KI' hlocal' hp'.ne eKI'⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
