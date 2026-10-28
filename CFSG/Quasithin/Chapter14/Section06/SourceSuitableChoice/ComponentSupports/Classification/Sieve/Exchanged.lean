module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.BorelNormal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentDiagram
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.PreservingModule

/-!
# The complete exchanged-component branch of the terminal model sieve

The literal image of M intersect K is proper and contains the component Borel.
For a rank-one model, uniqueness of the proper Sylow overgroup identifies it
with that Borel. Work in the actual subgroup J=⟨K^T⟩T and quotient J/O₂(J).
The exact overlap is self-normalizing, so the two components and their Borels
satisfy the established exchanged-action geometry.

The placed small quadratic actor either preserves or moves the component.
The respective original-module fixed-space theorems show that a Borel-fixed
seed is fixed by the residual. Its whole J-span is then fixed, contradicting
the original faithful quotient action. This excludes odd-degree PSL₂ and all
Suzuki components. Cubic Borel rank already excludes even-degree PSL₂.
Thus an exchanged component has the actual PSL₃(2) quotient, and the same
marking gives genuine parabolic exchange by N_T(K).

The terminal consumer retains H=Mc. Normal-component exclusions, natural
supports and suitable-vector assembly remain with qt-e-suitable-component-supports;
original 14.6.18 remains with qt-e-14625-source. No minimal-parabolic or
natural-module premise is added to the source specialization.

Source: Aschbacher--Smith 14.6.20, printed p.1037, F.9.18(5), pp.325--326,
and the Borel fixed-space calculation used in 15.3.65, p.1152.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]
/-- Normalizing an overlap whose intrinsic subgroup is a Sylow normalizer
already lies in that overlap. -/
private theorem overlap_self_normalizing_of_borel
    (D I : Subgroup G) (P : Sylow 2 D)
    (hB : I.subgroupOf D = normalizer (P : Set D)) :
    D ⊓ normalizer ((D ⊓ I : Subgroup G) : Set G) = D ⊓ I := by
  apply le_antisymm ?_ (le_inf inf_le_left (D ⊓ I).le_normalizer)
  rintro g ⟨hg,hn⟩
  have hh : (⟨g,hg⟩ : D) ∈ normalizer (I.subgroupOf D : Set D) := by
    apply mem_normalizer_iff.mpr
    intro x
    have hi := mem_normalizer_iff.mp hn (x : G)
    constructor
    · intro hx
      exact (hi.mp ⟨x.property,hx⟩).2
    · intro hx
      exact (hi.mpr ⟨D.mul_mem (D.mul_mem hg x.property) (D.inv_mem hg),hx⟩).2
  have hx : (⟨g,hg⟩ : D) ∈ I.subgroupOf D := by
    rw [hB] at hh ⊢
    rwa [P.normalizer_normalizer] at hh
  exact ⟨hg,hx⟩

omit [Finite G] in
/-- Intersecting after a quotient agrees with the intrinsic component map
when the quotient kernel lies in the original overlap. -/
private theorem intrinsic_overlap_map
    {D : Type*} [Group D] (q : G →* D) (K I : Subgroup G) (hk : q.ker ≤ I)
    (E : Type*) [Group E] (e : E ≃* K.map q) (r : K →* E)
    (hr : ∀ k : K, (e (r k) : D) = q k) :
    ((I.subgroupOf K).map r).map e.toMonoidHom =
      (I.map q).subgroupOf (K.map q) := by
  ext b
  constructor
  · rintro ⟨a,⟨k,hkI,rfl⟩,rfl⟩
    exact ⟨k,hkI,(hr k).symm⟩
  · intro hb
    obtain ⟨k,hkK,hkb⟩ := b.property
    obtain ⟨i,hi,hib⟩ := hb
    have hki : k * i⁻¹ ∈ q.ker := by
      change q (k * i⁻¹) = 1
      simp only [map_mul,map_inv,hkb,hib,Subgroup.subtype_apply,mul_inv_cancel]
    have hkI : k ∈ I := by
      have hh := I.mul_mem (hk hki) hi
      simpa only [inv_mul_cancel_right] using hh
    refine ⟨r ⟨k,hkK⟩,⟨⟨k,hkK⟩,hkI,rfl⟩,Subtype.ext ?_⟩
    exact (hr ⟨k,hkK⟩).trans hkb

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The marked M-overlap in an original component quotient is proper. -/
theorem source_component_overlap_image_ne_top
    {E : Type*} [Group E]
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* E) :
    (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≠ ⊤ := by
  intro he
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker ≤ M.subgroupOf K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
    exact (pCore_isPGroup.le_sylow_of_normal P).trans (hP ▸ subgroupOf_mono K hM.1.2)
  have hh := congrArg (Subgroup.comap q) he
  rw [comap_map_eq,sup_eq_left.mpr hk,comap_top] at hh
  exact source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    (fun k hk => show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hh ▸ mem_top _)

/-- In a rank-one model the actual overlap is exactly the marked Borel. -/
theorem source_component_overlap_eq_borel
    {E : Type*} [Group E] [Finite E]
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* E)
    (hfacts : ∀ S : Sylow 2 E, ChapterF.Source.RankOneSylowFacts S)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) :
    (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
      normalizer (((P : Subgroup K).map
        (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) : Set E) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  apply le_antisymm
  · apply (hfacts Pq).unique_maximal
    · exact map_mono (hP ▸ subgroupOf_mono K hM.1.2)
    · exact lt_top_iff_ne_top.mpr (source_component_overlap_image_ne_top
        hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK eK)
  · exact source_component_sylow_normalizer_le_image T M hsolv H hH.1 K hKH hK eK P hP


open Representation Representation.BinaryOffender
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.SourceModels
open GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio

/-- The actual exchanged odd-field rank-one component is impossible. Both
preserving and moving quadratic actors are treated on the original action. -/
theorem source_nonnormal_odd_rankOne_false
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 1 < f) (ho : Odd f) (hm : SourceModel (K ⧸ pCore 2 K) f)
    (hfacts : ∀ S : Sylow 2 (K ⧸ pCore 2 K), ChapterF.Source.RankOneSylowFacts S) : False := by
  let X := conjugateSpanBy K (T : Subgroup G)
  let J := X ⊔ (T : Subgroup G)
  have hXH : X ≤ H := conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer)
  have hJH : J ≤ H := sup_le hXH hH.1.2
  have hXJ : X ≤ J := le_sup_left
  have hKJ : K ≤ J := (le_conjugateSpanBy K _).trans hXJ
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    source_component_orbit_outside hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  have hHX : H ≤ normalizer (X : Set G) :=
    source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  have hTK : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro ht
    have he : X = K := le_antisymm (conjugateSpanBy_le le_rfl ht) (le_conjugateSpanBy K _)
    exact hn ((normal_subgroupOf_iff_le_normalizer hKH).mpr (he ▸ hHX))
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  let : Group.IsPerfect X := conjugateSpanBy_isPerfect K (T : Subgroup G)
  let : Group.IsPerfect (X.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXJ).symm.toMonoidHom) (subgroupOfEquivOfLe hXJ).symm.surjective
  let : (X.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr (hJH.trans hHX)
  have hp : IsPPerfect 2 (X.subgroupOf J) := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial ((X.subgroupOf J) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent ((X.subgroupOf J) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((X.subgroupOf J) ⧸ N) inferInstance
  have hr : pResidual 2 J = X.subgroupOf J :=
    pResidual_eq_of_isPPerfect_sup (X.subgroupOf J) ((T : Subgroup G).subgroupOf J)
      hp T.isPGroup'.comap_subtype (by
        rw [←subgroupOf_sup hXJ hTJ]
        change J.subgroupOf J = ⊤
        simp only [subgroupOf_self])
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,hfaith⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := (K.subgroupOf J).map q
  let S := ((T : Subgroup G).subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hmove : ¬ S ≤ normalizer (D : Set (J ⧸ pCore 2 J)) := by
    intro hsn
    have ht := map_le_iff_le_comap.mp hsn
    rw [normalizer_cComponent_quotient hc (pCore 2 J)] at ht
    apply hTK
    intro t htt
    have ht' := ht (show (⟨t,hTJ htt⟩ : J) ∈ (T : Subgroup G).subgroupOf J from htt)
    rwa [←subgroupOf_normalizer_eq hKJ] at ht'
  let : IsSimpleGroup (K ⧸ pCore 2 K) := source_component_quotient_simple
    hG T hempty hM hunique hmany hcard e hab hsolv J hJ K hKJ hc
  let : IsSimpleGroup D := ec.symm.isSimpleGroup
  let : Group.IsPerfect D := (hc.map_quotient (pCore 2 J)).perfect
  have hz : center D = ⊥ := by
    rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple D := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hD : IsComponent (J ⧸ pCore 2 J) D := ⟨(hc.map_quotient (pCore 2 J)).subnormal,inferInstance⟩
  have hAT : A.map q ≤ S := by
    apply map_mono
    have hTI : (T : Subgroup G) ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ J :=
      le_inf le_sup_right hTJ
    have hcore := pCoreIn_le_sylow _ (T.subtype hTI)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] at hcore
    exact hA.trans (subgroupOf_mono J hcore)
  have hX : X.subgroupOf J = conjugateSpanBy (K.subgroupOf J) ((T : Subgroup G).subgroupOf J) := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hXJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le hTJ]
  have hfaith' : A.map q ⊓ centralizer (componentOrbit D S : Set (J ⧸ pCore 2 J)) = ⊥ := by
    rw [GenerationOne.residual,hr,actorImage_internal,hX,map_conjugateSpanBy,
      conjugateSpanBy_eq_iSup_conj] at hfaith
    exact hfaith
  have hKTS : K ⊔ (T : Subgroup G) = J := by
    apply le_antisymm (sup_le hKJ hTJ)
    apply sup_le ?_ le_sup_right
    exact conjugateSpanBy_le le_sup_left (le_sup_right.trans (K ⊔ (T : Subgroup G)).le_normalizer)
  have hgenD : D ⊔ S = ⊤ := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hKJ hTJ,hKTS,subgroupOf_self]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  let Sq := (T.subtype hTJ).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSq : (Sq : Subgroup (J ⧸ pCore 2 J)) = S := rfl
  let I := (M.subgroupOf J).map q
  have hSI : S ≤ I := map_mono (subgroupOf_mono J hM.1.2)
  obtain ⟨P,hP⟩ := source_component_sylow T J K hTJ hKJ hc
  let qK := ec.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := qK) (ec.surjective.comp (QuotientGroup.mk'_surjective _))
  have hkerI : q.ker ≤ M.subgroupOf J := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hTJ)).trans (subgroupOf_mono J hM.1.2)
  have hInt : (M.subgroupOf K).map qK = I.subgroupOf D := by
    have hh := intrinsic_overlap_map q (K.subgroupOf J) (M.subgroupOf J) hkerI D
      (MulEquiv.refl D) (qK.comp (subgroupOfEquivOfLe hKJ).toMonoidHom) (fun _ => rfl)
    change (((M.subgroupOf J).subgroupOf (K.subgroupOf J)).map
      (qK.comp (subgroupOfEquivOfLe hKJ).toMonoidHom)).map (MonoidHom.id D) =
        I.subgroupOf D at hh
    rw [map_id] at hh
    have hmK : ((M.subgroupOf J).subgroupOf (K.subgroupOf J)).map
        (subgroupOfEquivOfLe hKJ).toMonoidHom = M.subgroupOf K := by
      ext k
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hk; exact ⟨⟨⟨k,hKJ k.property⟩,k.property⟩,hk,rfl⟩
    simpa only [←map_map,hmK] using hh
  have hB : I.subgroupOf D = normalizer (Pq : Set D) := by
    rw [←hInt]
    apply source_component_overlap_eq_borel hG T hempty hM hunique hmany hcard e hab hsolv
      J hJ K hKJ hc ec _ P hP
    intro R
    let R₀ := R.mapSurjective (f := ec.symm.toMonoidHom) ec.symm.surjective
    apply ChapterF.Source.Linear.transport ec R₀ R ?_ (hfacts R₀)
    change ((R : Subgroup D).map ec.symm.toMonoidHom).map ec.toMonoidHom = R
    rw [map_map]
    have hec : ec.toMonoidHom.comp ec.symm.toMonoidHom = MonoidHom.id D := by
      apply MonoidHom.ext
      intro x
      exact ec.apply_symm_apply x
    rw [hec]
    exact map_id _
  have hgeo := OriginalModule.Exchanged.geometry_of_generating_component hs.stronglyQuasithin
    Sq I D hD hz hgenD (fun hn => hmove (by let := hn; rw [normalizer_eq_top]; exact le_top))
    hSI (overlap_self_normalizing_of_borel D I Pq hB)
  have hrQ : componentOrbit D S = pResidual 2 (J ⧸ pCore 2 J) := by
    rw [componentOrbit,←conjugateSpanBy_eq_iSup_conj,←map_conjugateSpanBy,←hX,←hr,map_pResidual_quotient]
  have hAres : A.map q ⊓ centralizer (pResidual 2 (J ⧸ pCore 2 J) : Set (J ⧸ pCore 2 J)) = ⊥ :=
    hrQ ▸ hfaith'
  have hCB : ∃ R : Sylow 2 D, normalizer (R : Set D) = (I ⊓ D).subgroupOf D := by
    refine ⟨Pq,?_⟩
    rw [←hB]
    ext x
    simp only [mem_subgroupOf,mem_inf]
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hfixed : fixedSpace a.representation (I ⊓ pResidual 2 (J ⧸ pCore 2 J)) ≤
      fixedSpace a.representation (pResidual 2 (J ⧸ pCore 2 J)) := by
    have hnorm : S ≤ normalizer (pResidual 2 (J ⧸ pCore 2 J) : Set (J ⧸ pCore 2 J)) := by
      rw [normalizer_eq_top]; exact le_top
    by_cases hp : A.map q ≤ normalizer (D : Set (J ⧸ pCore 2 J))
    · exact OriginalModule.Exchanged.preserving_module_fixedSpace_le a.representation hgeo hnorm
        (pResidual_sup_sylow_eq_top Sq) hs a.faithful hD hAT hAE hAQ hAres hp hbound
        (hm.transport ((centerQuotientEquiv hz).trans ec.symm)) hf ho hCB
    · let := hAE.2
      exact OriginalModule.Exchanged.moving_module_fixedSpace_le a.representation hgeo hnorm
        a.faithful hD hAT hAQ hAres hp hbound hCB
  have hseed := source_overlap_seed_fixed hG T hempty hM hunique hmany hcard e hab J hJ a
  have hseedR : seedSpace a (localModule T M) ≤
      fixedSpace a.representation (pResidual 2 (J ⧸ pCore 2 J)) := by
    apply le_trans ?_ hfixed
    intro v hv b
    have hb : (b : J ⧸ pCore 2 J) ∈ actorImage J (M ⊓ J) := by
      obtain ⟨x,hx,he⟩ := b.property.1
      exact ⟨x,⟨hx,x.property⟩,he⟩
    exact hseed hv ⟨b,hb⟩
  have hwhole : (⊤ : Submodule (ZMod 2) _) ≤
      fixedSpace a.representation (pResidual 2 (J ⧸ pCore 2 J)) := by
    rw [←seedSpace_iSup_maps_eq_top a]
    apply iSup_le
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact (fixedSpace_stable_of_normal a.representation _ (mem_top g) w).2 (hseedR hw)
  have hbot : pResidual 2 (J ⧸ pCore 2 J) = ⊥ := by
    apply bot_unique
    intro d hd
    apply mem_bot.mpr
    apply a.faithful
    apply LinearMap.ext
    intro v
    simpa only [MonoidHom.comp_apply,Subgroup.subtype_apply,map_one,Module.End.one_apply] using hwhole Submodule.mem_top ⟨d,hd⟩
  exact (hc.map_quotient_ne_bot (pCore 2 J))
    (le_bot_iff.mp (hgeo.component_le.trans hbot.le))


omit hG T hempty hM hunique hmany hcard e hab hsolv in
private theorem rankOneFacts_transport {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : ∀ P : Sylow 2 B, ChapterF.Source.RankOneSylowFacts P)
    (P : Sylow 2 A) : ChapterF.Source.RankOneSylowFacts P := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply ChapterF.Source.Linear.transport e.symm Q P ?_ (h Q)
  change ((P : Subgroup A).map e.toMonoidHom).map e.symm.toMonoidHom = P
  rw [map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [he,map_id]

/-- Every odd defining degree in the exchanged PSL₂ branch is excluded. -/
theorem source_nonnormal_component_not_odd_psl_two
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) {f : ℕ} (hf : 1 < f) (ho : Odd f) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  exact source_nonnormal_odd_rankOne_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hf ho (.linearTwo F hF eF)
    (rankOneFacts_transport eF (ChapterF.Source.rankOneSylowFacts_psl2 F f (by omega) hF))

/-- The complete exchanged Suzuki branch is excluded on the original action. -/
theorem source_nonnormal_component_not_suzuki
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  exact source_nonnormal_odd_rankOne_false hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn (by omega : 1 < 2*m+1) ⟨m,rfl⟩ (.suzuki m hm rfl eK)
    (rankOneFacts_transport eK (ChapterF.Source.suzuki_rankOneSylowFacts m))

/-- An original exchanged component has precisely the binary PSL₃ quotient. -/
theorem source_nonnormal_component_linear_three
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 := by
  have hm := source_nonnormal_component_odd_models hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn
  rcases hm with ⟨f,hf,ho,hm⟩ | ⟨m,hm,⟨eK⟩⟩ | hl
  · exact (source_nonnormal_component_not_odd_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn (by omega) ho hm).elim
  · exact (source_nonnormal_component_not_suzuki hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm eK).elim
  · exact hl

/-- The exchanged-component quotient and genuine diagram action are both
constructed, using the same concrete PSL₃(2) marking. -/
theorem source_nonnormal_component_linear_three_diagram
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) :
    ∃ a : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL, ComponentParabolicSwap T K a := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := source_nonnormal_component_linear_three
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := eF.trans (Atlas.fieldEquivPSL 3 f)
  exact ⟨a,source_l3_component_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK a⟩

/-- Apply the complete exchanged-component model and diagram branch at H=Mc. -/
theorem terminal_nonnormal_component_linear_three_diagram
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ a : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL, ComponentParabolicSwap T K a :=
  source_nonnormal_component_linear_three_diagram hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
