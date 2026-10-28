module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.NoFiveComponent
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleAmalgam
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FaithfulResidual
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
public import Theory.GroupTheory.CComponent.ExceptionalQuotients
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.SpecificGroups.FFClassicalPrimeCore
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction

/-!
# Components of the original single-factor Goldschmidt quotient

A normal C-component of the actual join H₀ = H ⊔ L₁ that moves the
Sylow omega-center is faithful by characteristic two. The uniform A₅
hypothesis identifies its two-core quotient with A₅. This same A₅ survives
in H₀/O₃′(H₀), contradicting the direct normal-A₅ exclusion for Goldschmidt
triples. Thus every such component centralizes the whole omega-center.

Components of the literal quotient lift through its solvable prime-to-three
core. In particular, a quasisimple O² of that quotient would lift to O²(H₀)
itself, contradicting movement by the original O²(H).

This proves the component-centralization and quasisimple-residual exclusion
steps of Aschbacher--Smith 13.2.7, printed p.883. The cubic-product endgame
and the nonsolvable generation bound remain separate source obligations.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

private theorem normal_component_centralizes_omega
    (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J) (hJ : J.pCoreIn 2 ≠ ⊥)
    {A B : Subgroup J}
    (hqg : ChapterF.IsGoldschmidtTriple
      (A.map (QuotientGroup.mk' (pPrimeCore 3 J)))
      (B.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (K : Subgroup J) (hK : K.IsCComponent) [K.Normal] :
    K.map J.subtype ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let X := K.map J.subtype
  have hXJ : X ≤ J := map_subtype_le K
  have hX : X.subgroupOf J = K := comap_map_eq_self_of_injective J.subtype_injective K
  let : (X.subgroupOf J).Normal := hX.symm ▸ inferInstance
  have hlocal : X ∈ Chapter1.L G (T : Subgroup G) := by
    apply Chapter1.mem_L_of_cComponent hJ
      ⟨T.subtype hTJ,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ]⟩ hXJ
    rwa [hX]
  by_contra hm
  have hHe : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (d.hypothesis.qtke.evenCharacteristic T) ⟨hJ,hTJ⟩
  have hcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hZcore : omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient (J.pCoreIn 2) := by
    intro z hz
    have hz' := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hc : z ∈ centralizer (J.pCoreIn 2 : Set G) := fun x hx => hz'.2.2 x (hcoreT hx)
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hHe ⟨hTJ hz'.1,hc⟩,hz'.2.1,fun x hx => hz'.2.2 x (hcoreT hx)⟩
  have hfaith := Section03.Noncentrality.SupercriticalSource.faithful_signalizer_of_normal
    J X (omegaOneCenterAmbient (T : Subgroup G)) hHe hXJ
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal) hZcore
    (by intro he; exact hm (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
  obtain ⟨eX⟩ := d.uniform_A5 X
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T X).mpr ⟨hlocal,hfaith⟩)
  let f := K.equivMapOfInjective J.subtype J.subtype_injective
  let e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans eX
  have hthree : pPrimeCore 3 (K ⧸ pCore 2 K) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv e (Theory.SpecificGroups.alternating_threePrimeCore 5 (by decide))
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let eq : K.map q ≃* alternatingGroup (Fin 5) :=
    (CComponentExceptionalQuotient.quotientEquiv K hK.subnormal hthree).symm.trans e
  let : (K.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  exact ChapterF.SourceAssembly.goldschmidt_no_normal_five hqg (K.map q) eq

/-- Every normal C-component of the original single-factor join fixes the
whole Sylow omega-center. Both original Goldschmidt triples are retained. -/
theorem single_normal_component_centralizes_omega
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    ∀ K : Subgroup J, K.IsCComponent → K.Normal →
      K.map J.subtype ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro J A B q hg hqg K hK hn
  let := hn
  let eH : H.subgroupOf J ≃* H := subgroupOfEquivOfLe le_sup_left
  have he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH)).symm.trans hg.quotient_right.some⟩
  exact normal_component_centralizes_omega d J (hH.1.1.2.trans (show H ≤ J from le_sup_left))
    (single_borel_join_core_ne_bot d hH hB hZ he) hqg K hK

/-- Every ordinary component of the literal O₃′ quotient has a normal
C-component lift which centralizes the original omega-center. -/
theorem single_quotient_component_lift_centralizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    ∀ E : Subgroup (J ⧸ pPrimeCore 3 J), IsComponent (J ⧸ pPrimeCore 3 J) E →
      ∃ K : Subgroup J, K.IsCComponent ∧ K.Normal ∧ K.map q = E ∧
        K.map J.subtype ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro J A B q hSQ hg hqg E hE
  let : Group.IsSolvable (pPrimeCore 3 J) := hg.primeToThreeCore_solvable
  obtain ⟨K,hK,hmap⟩ := hE.isCComponent.exists_map_quotient_eq (pPrimeCore 3 J)
  have hn := (ChapterF.SourceAssembly.source_lemma_F_6_10_sqtk_quotient
    ChapterA.Section02.theoremA_knownSimple hSQ (MulEquiv.refl _) hqg hE).1
  have hKn : K.Normal := cComponent_normal_of_quotient_normal hK (pPrimeCore 3 J)
    (hmap.symm ▸ hn)
  exact ⟨K,hK,hKn,hmap,single_normal_component_centralizes_omega d hH hB hZ hg hqg K hK hKn⟩

/-- The original quotient cannot have a quasisimple two-residual: its
lift would be O²(J), forcing the original H to fix the whole omega-center. -/
theorem single_quotient_residual_not_quasisimple
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    ¬ IsQuasisimple (pResidual 2 (J ⧸ pPrimeCore 3 J)) := by
  intro J A B q hSQ hg hqg hr
  let := hr
  have hE : IsComponent (J ⧸ pPrimeCore 3 J) (pResidual 2 (J ⧸ pPrimeCore 3 J)) :=
    ⟨(inferInstance : (pResidual 2 (J ⧸ pPrimeCore 3 J)).Normal).isSubnormal,hr⟩
  obtain ⟨K,hK,hKn,hmap,hcent⟩ := single_quotient_component_lift_centralizes
    d hH hB hZ hSQ hg hqg _ hE
  let := hKn
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hn hquot
    let := hn
    let := hquot.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hKR : K ≤ primeToResidual 3 J :=
    (le_pResidual_of_isPPerfect K hp).trans_eq hg.twoResidual_eq_primeToThreeResidual
  have he : K = pResidual 2 J :=
    (eq_primeToResidual_of_coprime_quotient_image 3 (pPrimeCore 3 J) K
      pPrimeCore_coprime_card hKR (hmap.trans hqg.twoResidual_eq_primeToThreeResidual)).trans
      hg.twoResidual_eq_primeToThreeResidual.symm
  have hres : (pResidual 2 H).map H.subtype ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    rw [he] at hcent
    have hle := map_mono (f := J.subtype)
      (map_pResidual_le 2 (inclusion (show H ≤ J from le_sup_left)))
    rw [map_map] at hle
    exact hle.trans hcent
  exact residual_moves_omegaCenter T hH.1.1.2 hZ hres
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
