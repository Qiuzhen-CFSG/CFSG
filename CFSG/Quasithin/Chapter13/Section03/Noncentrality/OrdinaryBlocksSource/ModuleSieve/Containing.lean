module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.SourceEntry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual
public import Theory.GroupTheory.PGroup.SubgroupQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNoncontainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Projection

/-!
# The containing-component branch of the ordinary module sieve

If the original point residual lies in the selected component, the local
join is KT. Its reduced offender quotient modulo the actual component is
therefore a two-group, even when the reduced-action kernel has odd order.
This excludes the product rows and the outer A6-C3 row of B.5.6. The latter
is excluded by its nonperfect two-residual, without asserting any unproved
module coordinates for that row.

The original fixed line makes the quasisimple moved section nonsplit.
B.5.1(2) then gives Irr⁺ on that very section; its Sylow invariance constructs
an original ChosenModule on the literal moved subgroup. The final theorem
applies the earlier 12.2.2 module catalogue to this constructed choice.
The catalogue remains with qt-d-1222-modules; reduction (g), the surviving
A5 marking and final block assembly remain with qt-d-13314-ordinary-blocks.

Source: Aschbacher--Smith, B.5.1(2), B.5.6 and13.3.14(g), printed pp.99,
105 and892--893. No nonabelian full-span or later plane-noncentrality premise
is used.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction

private theorem linear_nontrivial (F : Type*) [Field F] (n : ℕ) (hn : 2 ≤ n) :
    Nontrivial (Matrix.SpecialLinearGroup (Fin n) F) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  refine ⟨⟨Matrix.SpecialLinearGroup.transvection hij (1 : F), 1, ?_⟩⟩
  intro he
  have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) F => g.val i j) he
  simp [Matrix.SpecialLinearGroup.transvection_coe, hij] at hh

private theorem component_le_product_factor {D : Type*} [Group D]
    {A B C : Subgroup D} (h : InternalProduct A B) (hC : IsComponent D C) :
    C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

private theorem product_factor_trivial_of_two_quotient {D : Type*} [Group D] [Finite D]
    {A B C : Subgroup D} [C.Normal] (h : InternalProduct A B)
    (hcore : pCore 2 D = ⊥) (hCA : C ≤ A) (hq : IsPGroup 2 (D ⧸ C)) :
    B = ⊥ := by
  let f := (QuotientGroup.mk' C).comp B.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply (eq_bot_iff_forall _).mpr
    intro b hb
    have hc : (b : D) ∈ C := (QuotientGroup.eq_one_iff (N := C) _).mp hb
    exact Subtype.ext (h.disjoint.le_bot ⟨hCA hc,b.property⟩)
  have hp : IsPGroup 2 B := hq.of_injective f hf
  have ht : (⊤ : Subgroup B) ≤ pCore 2 B :=
    le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩
  rw [h.second_twoCore hcore] at ht
  apply (eq_bot_iff_forall _).mpr
  intro b hb
  exact congrArg Subtype.val (ht (mem_top (⟨b,hb⟩ : B)))

private theorem no_product_of_component_two_quotient {D : Type*} [Group D] [Finite D]
    {A B C : Subgroup D} [C.Normal] [Nontrivial A] [Nontrivial B]
    (h : InternalProduct A B) (hC : IsComponent D C)
    (hcore : pCore 2 D = ⊥) (hq : IsPGroup 2 (D ⧸ C)) : False := by
  rcases component_le_product_factor h hC with ha | hb
  · exact (Subgroup.nontrivial_iff_ne_bot B).mp inferInstance
      (product_factor_trivial_of_two_quotient h hcore ha hq)
  · exact (Subgroup.nontrivial_iff_ne_bot A).mp inferInstance
      (product_factor_trivial_of_two_quotient h.swap hcore hb hq)

/-- A normal component with two-group quotient selects the full quasisimple
row in B.5.6. The outer A6-C3 shape is excluded by its nonperfect residual. -/
theorem quasisimple_row_of_component_two_quotient
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [C.Normal]
    (hC : IsComponent D C) (hq : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥)
    (h : NontrivialAdequateAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) := by
  let := hC.2
  have hF : generalizedFitting D = C :=
    generalizedFitting_eq_of_quasisimple_two_quotient C hq hcore
  cases h with
  | quasisimple _ c => exact hF ▸ ⟨c⟩
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    let : Group.IsSolvable D := Group.isSolvable_of_surjective
      (f := c.equiv.symm.toMonoidHom) c.equiv.symm.surjective
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c =>
    let : Nontrivial c.first := c.firstCase.nontrivial
    let : Nontrivial c.second := c.secondCase.nontrivial
    exact (no_product_of_component_two_quotient c.product hC hcore hq).elim
  | hyperplane c =>
    let := linear_nontrivial (ZMod 2) 3 (by decide)
    let : Nontrivial c.first := c.firstEquiv.symm.injective.nontrivial
    have hn : Nontrivial c.second := by
      cases c.secondCase with
      | linearThree _ _ h =>
        let := linear_nontrivial ChapterB.QuasisimpleSource.BinaryField.two.Carrier 3 (by decide)
        obtain ⟨e⟩ := h
        exact e.groupEquiv.symm.injective.nontrivial
      | linearTwo F h =>
        let := linear_nontrivial F.Carrier 2 (by decide)
        obtain ⟨e⟩ := h
        exact e.groupEquiv.symm.injective.nontrivial
    let := hn
    exact (no_product_of_component_two_quotient c.product hC hcore hq).elim
  | outerSixThree c =>
    let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
    have he : pResidual 2 D = C := le_antisymm
      (sInf_le ⟨inferInstance,hq⟩) (le_of_isPerfect_of_solvable_quotient C (pResidual 2 D))
    have hp : Group.IsPerfect (pResidual 2 D) := by rw [he]; infer_instance
    exact (c.not_perfect_two_residual hp).elim

open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- In the contrary containing branch of reduction (g), the literal reduced
offender quotient has exactly the selected component as its F*. This supplies
the complete B.5.1 action conclusion without any assumption on the centralizer
kernel or on the three-rank of that quotient. -/
theorem ordinary_containing_component_quasisimple_row
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    let B₀ := ((B.subgroupOf J).map q).subgroupOf N
    generalizedFitting N = B₀ ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) B₀) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let B₀ := Bq.subgroupOf N
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  let : Bq.Normal := (inferInstance : BJ.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B₀.Normal := inferInstance
  have hgen : BJ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ sourceOne L T P) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr hAK]
  have hquot : IsPGroup 2 ((J ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq (((T : Subgroup G).subgroupOf J).map q)
      (T.isPGroup'.comap_subtype.map q) (by
        rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN : IsPGroup 2 (N ⧸ B₀) := isPGroup_quotient_subgroupOf Bq N hquot
  obtain ⟨_,hcomp,hrows⟩ :=
    ordinary_selected_offender_entry_of_original_source d hmax eL escape h1332 K hK hqK hf
  let : IsQuasisimple B₀ := hcomp.2
  have hcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ
    (isPReduced_reducedPSubgroup (p := 2) (G := J)).quotient_pCore_eq_bot
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient B₀ hqN hcore,
    quasisimple_row_of_component_two_quotient (ρ.comp N.subtype) B₀ hcomp hqN hcore hrows⟩


open Chapter12.Section02 ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous

/-- The containing branch supplies an actual original Irr⁺ choice, on the
literal moved subgroup. The nonzero fixed line forces the nonsplit B.5.1 row. -/
theorem ordinary_containing_moved_module_chosen
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    Nonempty (ChosenModule T (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let σ := reducedRepresentation J
  let I := moved σ BJ
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hact : σ = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  have hI : I = moved ρ Bq := by
    change moved σ BJ = moved ρ (BJ.map q)
    rw [hact,moved_comp_map]
  have himage : subspaceImage J I = Diagonal.movedModule B (sourceOne L T P) T := by
    rw [hI]
    change subspaceImage J (subspaceCommutator ρ ⊤ (BJ.map q)) = _
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) BJ]
    change ((⁅W,BJ⁆.subgroupOf W).map W.subtype).map J.subtype = _
    rw [map_subgroupOf_eq_of_le (commutator_le_left W BJ),map_commutator,
      map_subgroupOf_eq_of_le hBJ]
    rfl
  have hfixed : I ⊓ fixedSpace σ BJ ≠ ⊥ := by
    intro he
    have hh := congrArg (ReducedNormal.subspaceImage J) he
    have heq : σ = ReducedNormal.representation J := by rfl
    rw [heq,ReducedNormal.subspaceImage_inf_fixedSpace J I B hBJ,
      ReducedNormal.subspaceImage_bot] at hh
    change subspaceImage J I ⊓ centralizer (B : Set G) = ⊥ at hh
    rw [himage] at hh
    exact ordinary_movedModule_fixed_ne_bot_of_actor_le d eL h1332 hc K hK hqK hf hAK hh
  obtain ⟨hBq,_,_⟩ :=
    ordinary_selected_offender_entry_of_original_source d hmax eL escape h1332 K hK hqK hf
  obtain ⟨_,⟨c⟩⟩ :=
    ordinary_containing_component_quasisimple_row d hmax eL escape h1332 K hK hqK hf hAK
  have hspace : c.sectionData.space.toSubmodule = moved ρ Bq := by
    rw [c.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hBq]
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (ρ.comp N.subtype) (Bq.subgroupOf N)) := by
    rw [hspace,fixedSpace_subgroupOf ρ Bq N hBq]
    intro hh
    apply hfixed
    rw [hI,hact,fixedSpace_comp_map]
    exact hh.disjoint.eq_bot
  have hirr : IsIrrPlus ρ Bq (moved ρ Bq) := by
    rw [←hspace]
    exact (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp (c.clause_two hn).1
  have hirr' : IsIrrPlus σ BJ I := by
    have hh := IsIrrPlus.map_embedding σ ρ q (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
      Function.injective_id (fun g w => by rw [hact]; rfl) BJ (moved ρ Bq) hirr
    simpa only [Submodule.map_id,←hI] using hh
  have hnormal : (T : Subgroup G).subgroupOf J ≤ normalizer (BJ : Set J) :=
    le_normalizer_of_normal
  have hstable : (T : Subgroup G).subgroupOf J ≤ subspaceStabilizer σ I :=
    subspaceCommutator_invariant_normalizer σ
      (by intro t ht v; simp) hnormal
  have hchoice : IsIrrPlusWith σ BJ ((T : Subgroup G).subgroupOf J) I := by
    refine ⟨hnormal,hirr'.choose,hirr',?_⟩
    apply le_antisymm
    · rw [orbitSpan_eq_self σ hstable]
      exact iSup_le fun S => iSup_le fun hS => hS.1
    · exact quotientImage_le_homogeneousPart σ hirr'.choose
  have hJ : J = B ⊔ (T : Subgroup G) := by
    change (B ⊔ sourceOne L T P) ⊔ (T : Subgroup G) = _
    rw [sup_eq_left.mpr hAK]
  have aux : ∀ (J' : Subgroup G) (I' : Submodule (ZMod 2) (Additive (ReducedModule J'))),
      J' = B ⊔ (T : Subgroup G) →
      IsIrrPlusWith (reducedRepresentation J') (B.subgroupOf J')
        ((T : Subgroup G).subgroupOf J') I' →
      subspaceImage J' I' = Diagonal.movedModule B (sourceOne L T P) T →
      Nonempty (ChosenModule T B (Diagonal.movedModule B (sourceOne L T P) T)) := by
    intro J' I' hj' hi' he'
    subst J'
    exact ⟨⟨I',hi',he'⟩⟩
  exact aux J I hJ hchoice himage

/-- Apply the genuine earlier module catalogue to the original moved subgroup,
after constructing its actual Irr⁺ choice and its Hypothesis12.2.3. -/
theorem ordinary_containing_module_alternatives
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    ∃ D : ChosenModule T (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T),
      ModuleAlternatives1222 D := by
  obtain ⟨D⟩ := ordinary_containing_moved_module_chosen d hmax eL escape h1332
    hc K hK hqK hf hAK
  exact ⟨D,modules _ _ (ordinary_selected_hypothesis1223 d h1332 K hqK hf) D⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
