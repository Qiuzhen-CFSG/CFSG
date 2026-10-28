module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Binary.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Binary.SourceEnvelope

/-!
# The source binary branch without the universal MS classification premise

Retain the original component, radical, Sylow intersection and generated plane
of original 14.6.10(5). Their omega-center containment and full movement feed
the narrow small-MS envelope theorem. The noncentral Sylow omega-center excludes
the abelian fixed-line case. The natural and doubled-natural plane calculations
then give rank three for the literal second parabolic.

The older conditional API remains available. This successor discharges its
binary source obligation using only the original ambient hypotheses.
Source: Aschbacher--Smith, original 14.6.10(5), printed pp.1028--1030;
Meierfrankenfeld--Stellmacher (1993), Section 4.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem small_quotient_of_binary (C : Subgroup G)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    SmallRankTwoQuotient C := by
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp
      (Matrix.PSL3Two.center_eq_bot.le ((centerCongr e ⟨x,hx⟩).property))
  let f := ((centralPreimageQuotientEquiv (pCore 2 C)).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)).trans e
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  exact Or.inl ⟨f.trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

omit [Finite G] in
private theorem normalizes_omega (A Q : Subgroup G)
    (h : A ≤ normalizer (Q : Set G)) :
    A ≤ normalizer (omegaOneCenterAmbient Q : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,
    ← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    mem_normalizer_iff_map_conj_eq.mp (h hg)]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original source plane and spans, with their natural module envelope
constructed from the literal component-radical MS pair. -/
theorem source_binary_plane_module_data_complete
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (he : Nonempty ((sourceGeneratedComponent T M Mc I d.H2 ⧸
      pCore 2 (sourceGeneratedComponent T M Mc I d.H2)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    let C := sourceGeneratedComponent T M Mc I d.H2
    let V := localModule T M
    Binary.PlaneConfiguration C V ∧
      Binary.ModuleEnvelope C (conjugateSpanBy V C) ∧
      conjugateSpanBy V (sourceGeneratedParabolic T M Mc I d.H2) = conjugateSpanBy V C ∧
      conjugateSpanBy V (sourceSecondParabolic T I d.H2) ≤ conjugateSpanBy V C ∧
      ¬ sourceSecondParabolic T I d.H2 ≤ normalizer (V : Set G) := by
  let V := localModule T M
  let A := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let I2 := sourceSecondParabolic T I d.H2
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
    (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
  let C := sourceGeneratedComponent T M Mc I d.H2
  let R := I1.pCoreIn 2
  let U := conjugateSpanBy V I0
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hI0,_,_,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I d.H2 hI hout d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  obtain ⟨K,_,_,_,_,hres,hCS,_,hmod,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  subst K
  have hCS' : C ⊔ ((T : Subgroup G) ⊓ I0) = I0 := hCS
  have hCI : C ≤ I0 := map_subtype_le _
  have hIC : I0 ≤ normalizer (C : Set G) := I0.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I0 (pResidual 2 I0))
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hspan : U = conjugateSpanBy V C := by
    change conjugateSpanBy V I0 = _
    rw [←hCS']
    exact conjugateSpanBy_sup_of_normalizes_seed V C _
      (inf_le_left.trans hTV) (inf_le_right.trans hIC)
  have hAI : A ≤ I0 := le_sup_left.trans le_sup_left
  have hAC : A ≤ C := by
    have hp := (isPPerfect_embedded_pResidual 2 (sourceResidual M Mc ⊓ I)).of_surjective
      (subgroupOfEquivOfLe hAI).symm.toMonoidHom
      (subgroupOfEquivOfLe hAI).symm.surjective
    have hh := map_mono (f := I0.subtype) (le_pResidual_of_isPPerfect (A.subgroupOf I0) hp)
    rwa [map_subgroupOf_eq_of_le hAI] at hh
  have hAV : A ≤ normalizer (V : Set G) :=
    (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc)).trans
      (le_normalizer_conjugateSpanBy _ M)
  have hmA : ⁅V,A⁆ = V := source_parabolic_plane_moved
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I hI.1 hout
  have hmU : ⁅U,C⁆ = U := (conjugateSpanBy_eq_commutator_of_seed V I0 C A
    hCI hIC hAC hmA.symm).symm
  obtain ⟨hi,hr,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  have hcore : (C ⊔ R).pCoreIn 2 = I0.pCoreIn 2 :=
    ChapterC.C27Source.residual_join_twoCore_eq I0 R hi.setup.radical_le hr
  have hUstar := source_generated_parabolic_span_le_star_module
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  have hUcomm : U ≤ ⁅omegaOneCenterAmbient (I0.pCoreIn 2),C⁆ :=
    hUstar.trans_eq (ChapterC.C27Source.residual_star_moved_eq_omegaCore_commutator
      I0 R hi.setup.radical_le hr)
  have hCcore : C ≤ normalizer (I0.pCoreIn 2 : Set G) := hCI.trans
    (I0.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I0 (pCore 2 I0)))
  have hUomega : U ≤ omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2) := by
    rw [hcore]
    exact hUcomm.trans (le_normalizer_iff_commutator_le_left.mp
      (normalizes_omega C _ hCcore))
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hUE : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUomega
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I0 hI0.1).1
  have hCN : (C.subgroupOf I0).Normal := normal_subgroupOf_of_le_normalizer hIC
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hCI
    hCN.isSubnormal
  have hms : SmallMSPair KnownSimple.IsKnownSimple C R :=
    smallMSPair_from_c27 hi hr (small_quotient_of_binary C he.some)
  have hplane : Binary.PlaneConfiguration C V :=
    ⟨hms.component_perfect,hspan ▸ hUE,hcard,⟨P,hP.le.trans (inf_le_left.trans (inf_le_left.trans hTV))⟩,
      A,hAC,isPPerfect_embedded_pResidual 2 _,hAV,hmA⟩
  let J := C ⊔ R
  let S := ((T : Subgroup G) ⊓ I0) ⊓ J
  have hI1I : I1 ≤ I0 := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  obtain ⟨Q,hQ⟩ := hSyl.restrict (show (T : Subgroup G) ⊓ I0 ≤ I1 from le_sup_right) hI1I
  have hRS0 : R ≤ (T : Subgroup G) ⊓ I0 := (pCoreIn_le_sylow I1 Q).trans_eq hQ
  have hJI : J ≤ I0 := sup_le hCI ((pCoreIn_le 2 I1).trans hI1I)
  have hJsub : (J.subgroupOf I0).IsSubnormal :=
    residual_overgroup_subnormal _ (fun x hx => mem_sup_left (mem_map_of_mem I0.subtype hx))
  have hS : Chapter1.IsSylowIn 2 S J :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hJI hJsub
  have hRS : R ≤ S := le_inf hRS0 le_sup_right
  have hZC : centralInvolutions T ≤ C :=
    (le_conjugateSpanBy _ M).trans ((le_conjugateSpanBy V I0).trans
      (hmod.2.trans (map_subtype_le _)))
  have hZO : centralInvolutions T ≤ FullSieve.SourceInterface.omegaCenterIn S := by
    intro z hz
    obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ z).mp hz
    apply (mem_omegaOneCenterAmbient_iff S z).mpr
    exact ⟨⟨⟨hzT,hCI (hZC hz)⟩,mem_sup_left (hZC hz)⟩,
      hz2,fun q hq => hzc q hq.1.1⟩
  have hnoncentral : ¬ FullSieve.SourceInterface.omegaCenterIn S ≤ FullSieve.SourceInterface.centerIn J := by
    intro hcent
    have hZcent : centralInvolutions T ≤ centralizer (C : Set G) := by
      intro z hz c hc
      obtain ⟨w,hw,heq⟩ := hcent (hZO hz)
      change (w : G) = z at heq
      have hh := congrArg Subtype.val (mem_center_iff.mp hw (⟨c,mem_sup_left hc⟩ : J))
      simpa only [Subgroup.coe_mul,heq] using hh
    have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
      H hH d.u d.mem_span d.index d.moves_core d.product_moves_core I hI.1.2.1 hout).1
    have hSylI := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
      hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
      d.local_normalizer hlocal I hI.1).1
    have hAout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
      hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
      I hI.1.2.1 hSylI hcover).2.2.2
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hMc,_⟩ :=
      source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
    exact hAout ((hAC.trans (le_centralizer_iff.mp hZcent)).trans_eq hMc.symm)
  have henv := Binary.envelope_of_smallMSPair C R S U hms he.some
    hS hRS hUomega hmU hnoncentral
  have hI2 : I2 ≤ I0 := le_sup_right
  have hmove : ¬ I2 ≤ normalizer (V : Set G) := by
    rw [← InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    intro hh
    apply hI0.1.2.2.2
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hh
  exact ⟨hplane,hspan ▸ henv,hspan,
    (conjugateSpanBy_mono le_rfl hI2).trans_eq hspan,hmove⟩

/-- The binary-linear-three branch of original 14.6.10(5), with the module
envelope proved from the actual small MS pair and every local premise discharged. -/
theorem source_second_parabolic_binary_rank_three_complete :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
  intro H hH d I hI _hpreferred he
  obtain ⟨hp,⟨E,f,hUE,hm⟩,_,hsub,hmove⟩ := source_binary_plane_module_data_complete
    hG T hempty hM hunique hmany hcard e hab H hH d I hI he
  let := hp.elementary
  have hspan := hm.elim (hp.span_card_of_natural hUE f)
    (hp.span_card_of_doubled_natural hUE f)
  exact (Binary.second_span_rank_three hp.card hspan hsub hmove).2.2

end CFSG.Quasithin.Chapter14.Section06
