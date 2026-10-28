module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSourceQuotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ComponentLift

/-!
# The faithful component of the original solvable-row amalgam

A.3.9 generates the solvable residual by C-components. Nonsolvability of
Ke/C_Ke(Ue) therefore selects a component moving the actual reduced orbit
module. Its commutator lies in its intrinsic signalizer module, proving
membership in the canonical faithful local family. The earlier 14.3.4
classification supplies its A₅ or PSL₃(2) two-core quotient, relative
normality and maximality. Subnormal core containment identifies its image
under Ke → Ke/O₃′(Ke) with that same simple model.

The application retains the original shifted involution, ambient group,
component and quotient map. Source: Aschbacher--Smith 14.3.31, printed
p.1003, with A.3.9, 1.2.6 and 14.3.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem amalgam_mem_HOver (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (K : Subgroup G)
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K))) :
    amalgamGroup F L K ∈ Chapter1.HOver G (T : Set G) := by
  let E := amalgamGroup F L K
  have h1E : F.Vi 1 ≤ E := (F.le_seed 1).trans
    (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K))
  have h1Q : F.Vi 1 ≤ E.pCoreIn 2 := by
    intro x hx
    exact ⟨⟨x,h1E hx⟩,hr.le_pCore (le_conjugateSpanBy _ _ hx),rfl⟩
  refine ⟨?_,sylow_le_amalgamGroup F L K⟩
  intro hzero
  have h1zero := le_bot_iff.mp (hzero ▸ h1Q)
  have hc := F.card 1 (by decide)
  rw [h1zero,card_bot] at hc
  norm_num at hc

/-- A C-component moves the original reduced orbit module and belongs to the
canonical faithful local family. -/
theorem source_amalgam_faithful_component (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) (K : Subgroup G)
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)))
    (hn : ¬ Group.IsSolvable (AmalgamQuotient F L K)) :
    ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn (amalgamGroup F L K) ∧
      C ∈ MainForward.faithfulLocalComponents T ∧
      ⁅amalgamModule F L K,C⁆ ≠ ⊥ := by
  let E := amalgamGroup F L K
  let W := amalgamModule F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hE := amalgam_mem_HOver chosen F K hr
  have hgen : cComponentLayer E = solvableResidual E :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hE.1)
  have hex : ∃ C : Subgroup E, C.IsCComponent ∧ ¬ C ≤ q.ker := by
    by_contra hno
    have hle : cComponentLayer E ≤ q.ker := by
      apply sSup_le
      intro C hC
      by_contra hCq
      exact hno ⟨C,hC,hCq⟩
    have hmap := (Subgroup.map_eq_bot_iff _).mpr hle
    rw [hgen,map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)] at hmap
    obtain ⟨n,heq⟩ := exists_derivedSeries_eq_solvableResidual (G := AmalgamQuotient F L K)
    exact hn ⟨n,heq.trans hmap⟩
  obtain ⟨C,hC,hCq⟩ := hex
  let D := C.map E.subtype
  have hD : D ∈ Chapter1.cComponentsIn E :=
    ⟨map_subtype_le _,by simpa only [D,subgroupOf,comap_map_eq_self_of_injective E.subtype_injective] using hC⟩
  have hWE : W ≤ E := conjugateSpanBy_le_self ((F.le_seed 1).trans
    (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
  have hm : ⁅W,D⁆ ≠ ⊥ := by
    intro hzero
    apply hCq
    intro c hc
    apply (QuotientGroup.eq_one_iff _).mpr
    intro w hw
    apply Subtype.ext
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
      (mem_map_of_mem E.subtype hc) w hw
  have hlocal := ((Chapter1.lemma_1_2_6 T hE).1 hD).2
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  let eD := subgroupOfEquivOfLe hD.1
  have hp' : IsPPerfect 2 (D.subgroupOf E) := hp.of_surjective
    eD.symm.toMonoidHom eD.symm.surjective
  have hle := (commutator_mono hr.le_reducedPSubgroup (le_refl (D.subgroupOf E))).trans
    (reduced_commutator_le_intrinsicModule _ hD.2.subnormal hp')
  have hmapped := map_mono (f := E.subtype) hle
  rw [map_commutator,map_subgroupOf_eq_of_le hWE,map_subgroupOf_eq_of_le hD.1,
    ←intrinsicSignalizerModule_map_of_injective E.subtype E.subtype_injective,
    map_subgroupOf_eq_of_le hD.1] at hmapped
  refine ⟨D,hD,?_,hm⟩
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (d.qtke.evenCharacteristic T)).mpr
  exact ⟨hlocal,fun he => hm (le_bot_iff.mp (he ▸ hmapped))⟩


private theorem prime_image_of_simple_core_quotient
    {D S : Type*} [Group D] [Finite D] [Group S] [Finite S] [IsSimpleGroup S]
    (C : Subgroup D) (hC : C.IsSubnormal)
    (e : (C ⧸ pCore 2 C) ≃* S) (hthree : 3 ∣ Nat.card S) :
    Nonempty (C.map (QuotientGroup.mk' (pPrimeCore 3 D)) ≃* S) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  have hc : pPrimeCore 3 (C ⧸ pCore 2 C) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv e (pPrimeCore_eq_bot_of_simple hthree)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcore : pPrimeCore 3 C = pCore 2 C := by
    have he := pPrimeCore_comap_eq_of_surjective_coprime 3 q
      (QuotientGroup.mk'_surjective _) hcop
    rw [hc] at he
    exact he.symm.trans (QuotientGroup.ker_mk' _)
  let p := QuotientGroup.mk' (pPrimeCore 3 D)
  have hk : (p.subgroupMap C).ker = pCore 2 C := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    apply le_antisymm
    · rw [←hcore]
      exact le_sSup ⟨inferInstance,pPrimeCore_coprime_card.of_dvd_right
        (card_comap_dvd_of_injective _ _ C.subtype_injective)⟩
    · intro c hc
      exact ChapterF.twoCore_le_primeToThreeCore
        (pCoreIn_le_of_subnormal 2 hC (mem_map_of_mem C.subtype hc))
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (p.subgroupMap_surjective C)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans e)⟩

/-- A moving component of the actual orbit-action quotient has its original
faithful classification and a simple subnormal image in the prime-to-three quotient. -/
theorem source_amalgam_classified_component (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) (K : Subgroup G)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)))
    (hn : ¬ Group.IsSolvable (AmalgamQuotient F L K)) :
    let E := amalgamGroup F L K
    ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
      C ∈ MainForward.faithfulLocalComponents T ∧
      ⁅amalgamModule F L K,C⁆ ≠ ⊥ ∧
      (Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)) ∧
      (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T ∧
      let p := QuotientGroup.mk' (pPrimeCore 3 E)
      ((C.subgroupOf E).map p).IsSubnormal ∧
      (Nonempty ((C.subgroupOf E).map p ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((C.subgroupOf E).map p ≃* Matrix.PSL3Two.PSL)) := by
  obtain ⟨C,hC,hf,hm⟩ := source_amalgam_faithful_component d chosen F K hr hn
  have hh := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hf
  obtain ⟨hmodel,hN,hmax⟩ := classification C hh.1 hh.2
  let E := amalgamGroup F L K
  let j : C.subgroupOf E ≃* C := subgroupOfEquivOfLe hC.1
  let jq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  refine ⟨C,hC,hf,hm,hmodel,hN,hmax,
    hC.2.subnormal.map (QuotientGroup.mk'_surjective _),?_⟩
  rcases hmodel with ha | ha <;> obtain ⟨a⟩ := ha
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact Or.inl (prime_image_of_simple_core_quotient _ hC.2.subnormal (jq.trans a)
      (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]))
  · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    exact Or.inr (prime_image_of_simple_core_quotient _ hC.2.subnormal (jq.trans a)
      (by rw [Matrix.PSL3Two.card_PSL]; decide))

/-- Apply the faithful classification to the same shifted amalgam that satisfies
F.6.18, retaining the original component and literal quotient image. -/
theorem source_solvable_faithful_amalgam (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      E ≤ centralizer ({e} : Set G) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        ⁅amalgamModule F L K,C⁆ ≠ ⊥ ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL)) ∧
        (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T ∧
        let p := QuotientGroup.mk' (pPrimeCore 3 E)
        ((C.subgroupOf E).map p).IsSubnormal ∧
        (Nonempty ((C.subgroupOf E).map p ≃* alternatingGroup (Fin 5)) ∨
          Nonempty ((C.subgroupOf E).map p ≃* Matrix.PSL3Two.PSL)) := by
  obtain ⟨l,e,hl,he,heI,heT,hE,hr,_,_,_,_,_,_,_,_,_,hn⟩ :=
    source_solvable_source_classification d earlier hq chosen structural alternatives F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,hE,
    source_amalgam_classified_component d chosen F _ classification hr hn⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
