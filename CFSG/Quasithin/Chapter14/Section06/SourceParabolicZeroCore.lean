module

public import CFSG.Quasithin.Chapter14.Section06.SourceSecondParabolic
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow

/-!
# Excluding the generated zero-core branch in 14.6.6(6)

The literal two parabolics have the same local Sylow subgroup. Their
S₃ quotients and characteristic-two properties are proved before considering
their join. The first characteristic-two calculation uses the normal plane
and its two-group centralizer; the second uses O₂(H)-normalization.

If the join has trivial two-core, these facts construct corrected F.1.1.
The explicit cubic F.1.12 size input bounds the common subgroup by 128.
Its index at most four in T contradicts the original order threshold.
The final consumer consequently discharges the nontrivial-core premise
of the generated choice and then applies 14.6.10(1–2).

Source: Aschbacher–Smith, 14.6.6(6), pp.1023–1024, and 14.6.10, p.1028.
The only recognition input is `ChapterF.Source.CubicF112SizeInput`;
no ambient Sylow conclusion for the join is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem characteristic_of_normal_module
    (P V : Subgroup G) (hV : IsPGroup 2 V) (hVP : V ≤ P)
    (hN : P ≤ normalizer (V : Set G))
    (hC : P ⊓ centralizer (V : Set G) ≤ P.pCoreIn 2) :
    generalizedFitting P = pCore 2 P := by
  have hVR := le_pCoreIn_of_normalizes hV hVP hN
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro x hx
  have hxV : (x : G) ∈ centralizer (V : Set G) := by
    intro v hv
    obtain ⟨a,ha,he⟩ := hVR hv
    exact he ▸ congrArg P.subtype (hx a ha)
  obtain ⟨a,ha,he⟩ := hC ⟨x.property,hxV⟩
  exact (Subtype.ext he : a = x) ▸ ha

open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The zero-core contradiction of 14.6.6(6). All local F.1.1 premises
are derived from the literal source parabolics. -/
theorem source_generated_twoCore_ne_bot
    (recognition : ChapterF.Source.CubicF112SizeInput.{u})
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hlarge : 512 < Nat.card T) :
    (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔
      ((pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I))).pCoreIn 2 ≠ ⊥ := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let V := localModule T M
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ I
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let I1 := R ⊔ S
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
  have hTuS : Tu ≤ S := le_inf inf_le_left hI.1.2.1
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSylI := (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hSyl1 : Chapter1.IsSylowIn 2 S I1 := hSylI.restrict le_sup_right hI1I
  have hquot1 := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSylI hcover).1
  have hsecond := suitable_second_parabolic_data h u hu H2 S hTuS hS0 hi.1 hi.2.2.2.1
    hSylH2 hH2kernel hH2quot hlocal
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hVU : V ≤ conjugateSpanBy V Mc := le_conjugateSpanBy _ _
  have huU : u ∈ conjugateSpanBy V Mc := (conjugateSpanBy_mono le_rfl hHMc) hu
  have hrank := Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e
  have hVT : V ≤ (T : Subgroup G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using hrank.seed_le_sylow
  have hVTu : V ≤ Tu := by
    let := hab
    intro v hv
    refine ⟨hVT hv,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg (conjugateSpanBy V Mc).subtype
      (mul_comm (⟨v,hVU hv⟩ : conjugateSpanBy V Mc) ⟨u,huU⟩)
  have hI1J : I1 ≤ L ⊔ (T : Subgroup G) := sup_le
    (((map_subtype_le _).trans inf_le_left).trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hchar1 : generalizedFitting I1 = pCore 2 I1 := by
    apply characteristic_of_normal_module I1 V
      (by
        let := rankTwoSeed_elementary hrank
        change IsPGroup 2 (localModule T M)
        rw [← Section02.rankTwoSeed_eq_localModule]
        exact IsElementaryAbelian.isPGroup 2 (rankTwoSeed T M)) ((hVTu.trans hTuS).trans le_sup_right)
      (by
        simpa only [Section02.rankTwoSeed_eq_localModule] using
          (hI1J.trans ((sup_le hrank.L_le hrank.sylow_le).trans
            RankTwoHypothesis.M_normalizes_seed)))
    have hc : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      simpa only [Section02.rankTwoSeed_eq_localModule] using hrank.centralizer
    exact (le_inf inf_le_left ((le_inf (inf_le_left.trans hI1J) inf_le_right).trans hc.le)).trans
      (inf_pCoreIn_le_of_le 2 hI1J)
  have hSindex : S.relIndex (T : Subgroup G) ≤ 4 := by
    have hTuindex : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
    have hh := relIndex_le_of_le_left (L := (T : Subgroup G)) hTuS
      (show Tu.relIndex (T : Subgroup G) ≠ 0 by rw [hTuindex]; decide)
    simpa only [hTuindex] using hh
  exact ChapterF.Source.generated_twoCore_ne_bot_of_cubic_size recognition (T : Subgroup G)
    ![I1,I2] S inf_le_left hSindex hlarge
    (by rw [Fin.forall_fin_two]; exact ⟨hSyl1,hsecond.1⟩)
    (by rw [Fin.forall_fin_two]; exact ⟨hquot1,hsecond.2.1⟩)
    (by rw [Fin.forall_fin_two]; exact ⟨hchar1,hsecond.2.2⟩)

/-- The actual generated source application of 14.6.10(1–2), with its
factorization, generation and nontrivial generated-core premises discharged.
The earlier cubic F.1.12 recognition input remains explicit. -/
theorem source_generated_parabolic_cores_of_f112
    (recognition : ChapterF.Source.CubicF112SizeInput.{u})
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    I0 ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) ∧
      (T : Subgroup G) ⊓ I0 = (T : Subgroup G) ⊓ I ∧
      I1 ⊔ I2 = I0 ∧ I2 ≤ H2 ∧
      (I1.pCoreIn 2).characteristicNormalizerClosure ≤ M ∧
      I1.pCoreIn 2 ≠ ⊥ ∧ I1.pCoreIn 2 ≠ I2.pCoreIn 2 := by
  have hlarge := (source_lemma_14_6_9_order hG T hempty hM hunique hmany hcard e hab H hH
    hcoreIndex hrank).2
  have hcore := source_generated_twoCore_ne_bot hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal recognition I H2 hI hout hSylH2
      hH2kernel hH2quot (by norm_num at hlarge; omega)
  exact source_generated_parabolic_cores hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I H2 hI hout hSylH2 hH2out
      hcoreIndex hrank hcore

end CFSG.Quasithin.Chapter14.Section06

