module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.LocalReductions
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.MaximalTwoLocalCore
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingControl
public import Theory.GroupTheory.Fitting.OutsideComponent
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction

/-!
# Preparing the terminal component branch of original 15.2.23

Put NI = M ∩ I and R = O₂(NI). The faithful S₃ quotient NI/C_NI(V)
annihilates R. Normal two-core restriction then identifies R with O₂(M),
so maximal two-locality supplies the radical normalizer and characteristic
normalizer control required by C.2.3. This proves the applicability step
15.2.19(2) from the exact action conclusion of 15.2.18(3ii).

Under F*(I) = O₂(I), the independent no-chi-block result and C.2.6 put
O₂,F(I) inside NI. A.4.4 rules out O₂,F*(I) inside NI, since it would put
the original K = O²(H) in M. The quotient component therefore lifts to an
actual escaping C-component X of I. The source two-orbit theorem makes
K normalize X. Every embedding, core quotient and normality statement
retains its original ambient subgroup.

Once R-normalization is separately established, the last theorem applies
the full known-simple B.5.1 classifier to the literal C.2.7 star action.
It imposes no bound on the Sylow order. The bounded SmallModels theorem
is not applicable without an additional bound, and would discard L₅(2).

The source Omega/index-six construction, C.2.4(1) block argument proving
R-normalization, and terminal SL₃, L₄ and L₅ exclusions remain required.
The no-chi-block premise belongs to the independent preliminary exclusion;
it is not asserted here. This module does not prove the final 15.2.23
contradiction. Its shared preparation is separate from final assembly so
that the remaining branches can import these proved steps without a cycle.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.18(3), 15.2.19(2), and 15.2.23, printed pp.1113--1117;
C.2.3--7, pp.144--147; A.4.4, p.58; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The core equality in 15.2.19(2), once the actual S₃ action kills O₂(NI). -/
theorem intersection_core_eq_of_centralizes (hI : PlaneEscapes Mc ZS I)
    (hR : (M ⊓ I).pCoreIn 2 ≤ centralizer (V : Set G)) :
    (M ⊓ I).pCoreIn 2 = M.pCoreIn 2 := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hsource.prepared.normalized.trans (normalizer_le_normalizer_centralizer _))
  have hred := hsource.prepared.reduced T hsource.maximal.1.2
  have hQC : pCore 2 M ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,hsource.prepared.le_selected hv⟩ hv)
  have hCC : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQC]
  have hCI : C.map M.subtype ≤ M ⊓ I := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (d.module_centralizer_le hI))
  have hRC : (M ⊓ I).pCoreIn 2 ≤ C.map M.subtype := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf hR ((pCoreIn_le 2 _).trans inf_le_left)
  have hCQ : (C.map M.subtype).pCoreIn 2 = M.pCoreIn 2 := by
    rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCC]
    rfl
  apply le_antisymm
  · have hh := inf_pCoreIn_le_of_le 2 hCI
    rwa [inf_eq_right.mpr hRC,hCQ] at hh
  · have hQNI : M.pCoreIn 2 ≤ M ⊓ I := (map_mono hQC).trans hCI
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) hQNI
      (inf_le_left.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))

omit d in
include hsource in
/-- The literal radical normalizer is NI, using maximal two-locality of M. -/
theorem intersection_core_normalizer (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) :
    I ⊓ normalizer ((M ⊓ I).pCoreIn 2 : Set G) = M ⊓ I := by
  rw [hcore,maximalTwoLocal_normalizer_core hsource.maximal.1.1,inf_comm]

omit d in
include hsource in
/-- Characteristic-normalizer control in I follows from the original core of M. -/
theorem intersection_core_characteristic_control
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) :
    (((M ⊓ I).pCoreIn 2).subgroupOf I).characteristicNormalizerClosure ≤
      (M ⊓ I).subgroupOf I := by
  have hRI : (M ⊓ I).pCoreIn 2 ≤ I := (pCoreIn_le 2 _).trans inf_le_right
  have hc : ((M ⊓ I).pCoreIn 2).characteristicNormalizerClosure ≤ M := by
    rw [hcore,maximalTwoLocal_characteristicNormalizer_core hsource.maximal.1.1]
  have hh := characteristicNormalizerClosure_subgroupOf_le hRI hc
  exact fun x hx => ⟨hh hx,x.property⟩

omit d in
include hsource in
/-- All of C.2.3 on the actual I, O₂(NI), NI; only the core equality is input. -/
theorem intersection_pushingUpSetup (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) :
    PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  let R := (M ⊓ I).pCoreIn 2
  let N := M ⊓ I
  have hRN : R ≤ N := pCoreIn_le 2 N
  have hRI : R ≤ I := hRN.trans inf_le_right
  have hRne : R ≠ ⊥ := by
    change (M ⊓ I).pCoreIn 2 ≠ ⊥
    rw [hcore]
    exact maximalTwoLocal_core_ne_bot hsource.maximal.1.1
  have hnorm : normalizer (R.subgroupOf I : Set I) = N.subgroupOf I := by
    rw [←subgroupOf_normalizer_eq hRI]
    ext x
    change (x : G) ∈ normalizer (R : Set G) ↔ (x : G) ∈ N
    constructor
    · intro hx
      exact (intersection_core_normalizer (hsource := hsource) hcore).le ⟨x.property,hx⟩
    · intro hx
      exact ((intersection_core_normalizer (hsource := hsource) hcore).ge hx).2
  have hrad : IsPRadical 2 (R.subgroupOf I) := by
    refine ⟨?_,?_⟩
    · intro he
      apply hRne
      have hh := congrArg (map I.subtype) he
      simpa only [map_subgroupOf_eq_of_le hRI,Subgroup.map_bot] using hh
    · change (normalizer (R.subgroupOf I : Set I)).pCoreIn 2 = R.subgroupOf I
      rw [hnorm]
      apply map_injective I.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
        map_subgroupOf_eq_of_le (show N ≤ I from inf_le_right),map_subgroupOf_eq_of_le hRI]
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple I := by
    have hQ : pCore 2 I ≠ ⊥ := by
      intro he
      apply hI.1
      change (pCore 2 I).map I.subtype = ⊥
      rw [he,Subgroup.map_bot]
    obtain ⟨L,hL,hIL⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hQ
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIL)).mp
      ((hsource.ambient.twoLocal_sqtk hL.1).subgroup (I.subgroupOf L))
  refine ⟨hsqtk,hRI,inf_le_right,hrad,intersection_core_characteristic_control (hsource := hsource) hcore,?_⟩
  have hnR : N ≤ normalizer (R : Set G) := N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  let : (R.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hnR
  have hcl : (normalClosure (R.subgroupOf N : Set N)).map N.subtype = R := by
    rw [Subgroup.normalClosure_eq_self,map_subgroupOf_eq_of_le hRN]
  rw [hcl]
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨isPGroup_pCoreIn 2 N, le_rfl, ?_⟩
  intro U hU hRU hUN
  exact le_antisymm hUN hRU

/-- Original 15.2.19(2) with precisely the missing small-action premise exposed. -/
theorem intersection_pushingUpSetup_of_core_centralizes (hI : PlaneEscapes Mc ZS I)
    (hR : (M ⊓ I).pCoreIn 2 ≤ centralizer (V : Set G)) :
    PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) :=
  intersection_pushingUpSetup (hsource := hsource) hI (d.intersection_core_eq_of_centralizes hI hR)

/-- The generalized-Fitting preimage cannot lie in NI: A.4.4 would make its
core normal in I and put the original residual K in M. -/
theorem fitting_preimage_not_le_intersection
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) :
    ¬ (generalizedFitting (I ⧸ pCore 2 I)).comap
      (QuotientGroup.mk' (pCore 2 I)) ≤ (M ⊓ I).subgroupOf I := by
  intro hle
  have hp : twoGeneralizedFittingPreimage I ≤ I ⊓ M := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x.property,(hle hx).1⟩
  have ha : IntersectionAlternative
      (twoCoreQuotientImage I (twoGeneralizedFittingPreimage I)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (I ⧸ pCore 2 I)).subgroupOf
        (generalizedFitting (I ⧸ pCore 2 I))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have he := lemma_A_4_4_1 I M (twoGeneralizedFittingPreimage I)
    (twoCore_le_fittingPreimage I) hp ha
  rw [inf_comm I M,hcore] at he
  have hIM : I ≤ M := by
    rw [←maximalTwoLocal_normalizer_core hsource.maximal.1.1,←he]
    exact I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact d.residual_not_le (((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans hIM)

omit d [Finite G] in
/-- The literal S₃ action in 15.2.18(3ii) kills the original intersection core.
The kernel equality identifies the action as NI/C_NI(V), not an arbitrary
symmetric-three quotient. -/
theorem intersection_core_centralizes_of_symmetricThree
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    (M ⊓ I).pCoreIn 2 ≤ centralizer (V : Set G) := by
  have htwo : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hn : ((pCore 2 (M ⊓ I : Subgroup G)).map f).Normal :=
    (inferInstance : (pCore 2 (M ⊓ I : Subgroup G)).Normal).map f hf
  have hm : (pCore 2 (M ⊓ I : Subgroup G)).map f ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hk : pCore 2 (M ⊓ I : Subgroup G) ≤ f.ker :=
    (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans_eq htwo))
  rw [hker] at hk
  rintro x ⟨y,hy,rfl⟩
  exact hk hy

/-- Source 15.2.19(2), with only the faithful S₃ action of 15.2.18(3ii)
remaining to be supplied by the original Omega-action construction. -/
theorem intersection_pushingUpSetup_of_symmetricThree (hI : PlaneEscapes Mc ZS I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) :=
  d.intersection_pushingUpSetup_of_core_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)

omit d in
include hsource in
/-- C.2.6 on the actual I and R = O₂(NI). The no-chi-block premise is
precisely the preliminary exclusion owned by BlockExclusion. -/
theorem fittingCore_le_intersection_of_no_chi
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    twoFittingCore I ≤ (M ⊓ I).subgroupOf I := by
  have hs := intersection_pushingUpSetup (hsource := hsource) hI hcore
  apply ChapterC.Section02Source.fittingCore_le_of_no_moved_alternatingThree
    hs.sqtk _ _ hs.radical hs.characteristic_control
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  intro X hX _ ha
  exact hno X ⟨hX,Or.inr ⟨3,by decide,ha⟩⟩

/-- Select an actual escaping C-component through the quotient by O₂(I).
This is the component-selection paragraph of 15.2.23; it does not yet
assert that the radical normalizes this component. -/
theorem escaping_component_of_no_chi
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup I, X.IsCComponent ∧ IsQuasisimple (X ⧸ pCore 2 X) ∧
      generalizedFitting X = pCore 2 X ∧ ¬ X ≤ (M ⊓ I).subgroupOf I :=
  exists_characteristicTwo_cComponent_outside _
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
    (fittingCore_le_intersection_of_no_chi (hsource := hsource) hI hfit hcore hno)
    (d.fitting_preimage_not_le_intersection hI hcore)

/-- The same selected component, transported back by the literal inclusion I→G.
All component normality remains relative to I. -/
theorem escaping_ambient_component_of_no_chi
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup G, X ∈ Chapter1.cComponentsIn I ∧
      IsQuasisimple (X ⧸ pCore 2 X) ∧ generalizedFitting X = pCore 2 X ∧
      ¬ X ≤ M ⊓ I := by
  obtain ⟨Y,hY,hq,hf,hout⟩ := d.escaping_component_of_no_chi hI hfit hcore hno
  let X := Y.map I.subtype
  let e : Y ≃* X := Y.equivMapOfInjective I.subtype I.subtype_injective
  have hXC : X ∈ Chapter1.cComponentsIn I := by
    refine ⟨map_subtype_le _,?_⟩
    have he : X.subgroupOf I = Y :=
      comap_map_eq_self_of_injective I.subtype_injective Y
    rwa [he]
  let := hq
  have hqX : IsQuasisimple (X ⧸ pCore 2 X) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hfX : generalizedFitting X = pCore 2 X := by
    rw [←map_generalizedFitting_equiv e,hf,pCore_map_iso]
  refine ⟨X,hXC,hqX,hfX,?_⟩
  intro hh
  exact hout (fun y hy => hh (mem_map_of_mem I.subtype hy))

/-- Source application using the exact faithful action quotient in 15.2.18(3ii).
Only that action and the independent no-chi-block result remain as inputs. -/
theorem escaping_component_of_symmetricThree
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup G, X ∈ Chapter1.cComponentsIn I ∧
      IsQuasisimple (X ⧸ pCore 2 X) ∧ generalizedFitting X = pCore 2 X ∧
      ¬ X ≤ M ⊓ I :=
  d.escaping_ambient_component_of_no_chi hI hfit
    (d.intersection_core_eq_of_centralizes hI
      (intersection_core_centralizes_of_symmetricThree f hf hker)) hno

/-- The original two-residual K fixes every C-component of I. The source
orbit theorem gives index at most two, and two-perfectness kills that action. -/
theorem residual_normalizes_component (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : X.IsCComponent) :
    (pResidual 2 H).map H.subtype ≤ normalizer (X.map I.subtype : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  let A := K.subgroupOf I
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hs := Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  have hAN : A ≤ normalizer (X : Set I) := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hX with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact le_top
    · let N := normalizer (X : Set I)
      let : N.Normal := normal_of_index_eq_two hi
      have hquot : IsPGroup 2 (I ⧸ N) := IsPGroup.of_card (n := 1) (by
        simpa only [←index_eq_card,pow_one] using hi)
      exact (le_pResidual_of_isPPerfect A hpA).trans (sInf_le ⟨inferInstance,hquot⟩)
  intro k hk
  exact X.le_normalizer_map I.subtype
    (mem_map_of_mem I.subtype (hAN (show (⟨k,hKI hk⟩ : I) ∈ A from hk)))

/-- The original component-selection consumer, including K-normalization.
The action kernel is exactly C_NI(V); no model tag or final contradiction
is part of the input. -/
theorem escaping_component_with_residual_normalization
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup G, X ∈ Chapter1.cComponentsIn I ∧
      IsQuasisimple (X ⧸ pCore 2 X) ∧ generalizedFitting X = pCore 2 X ∧
      ¬ X ≤ M ⊓ I ∧
      (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
  obtain ⟨X,hX,hq,hfX,hout⟩ := d.escaping_component_of_symmetricThree hI hfit f hf hker hno
  have hn := d.residual_normalizes_component hI hX.2
  rw [map_subgroupOf_eq_of_le hX.1] at hn
  exact ⟨X,hX,hq,hfX,hout,hn⟩

omit d in
include hsource in
open Chapter1.RadicalExclusions.ModelReduction
  Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
  Representation Representation.BinaryOffender in
/-- Apply the unrestricted B.5.1 source classifier to the literal C.2.7 star
action. Radical normalization is displayed separately: it is the remaining
C.2.4(1) block argument, not a consequence of K-normalization. No small
Sylow bound is imposed, so the L₅(2) source row is retained. -/
theorem component_moved_section_from_normalization
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    {X : Subgroup G} (hX : X ∈ Chapter1.cComponentsIn I)
    (hq : IsQuasisimple (X ⧸ pCore 2 X))
    (hf : generalizedFitting X = pCore 2 X) (hout : ¬ X ≤ M ⊓ I)
    (hn : (M ⊓ I).pCoreIn 2 ≤ normalizer (X : Set G)) :
    let R := (M ⊓ I).pCoreIn 2
    let ρ := starRepresentation X R
    let J := Representation.BinaryOffender.offenderSubgroup ρ
    starImage X R X ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp J.subtype) ((starImage X R X).subgroupOf J)) := by
  exact ChapterC.C27Source.star_moved_section_from_source
    ⟨intersection_pushingUpSetup (hsource := hsource) hI hcore,hX,hq,hf,hout,hn⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
