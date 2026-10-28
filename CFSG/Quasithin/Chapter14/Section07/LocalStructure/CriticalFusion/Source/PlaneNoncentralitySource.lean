module

public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Chosen
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.LinearThreeCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.NaturalSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceNoncentrality

/-!
# Plane noncentrality on the original Chapter 14 data

Assume the original point core centralizes the original plane. The natural
parabolic span then puts U in Ω₁(Z(Q_H)). The actual section centralizer
identifies C_H(U)=Q_H, making U a reduced subgroup of H=KT. Its natural
SL₂(4) section and U=[U,K] prove Irr⁺ minimality. We construct a literal
ChosenModule T K U, and the same commutator identity proves that K belongs
to the original faithful local family.

The earlier universal 13.3.2(3) A₅ alternative now applies to this actual U.
It gives the alternating natural module of order sixteen. But the original
natural SL₂(4) quotient already has order sixteen and its kernel contains
the original point of order two. This contradiction proves the needed
13.3.14 specialization and supplies [U,Q_H]=V₁ to the existing consumer.

The only new earlier-source input is AlternatingFiveModules1332, whose
producer remains qt-13-03-preliminaries. The universal all-branches 13.3.14
is not asserted here. No noncentrality, chosen module, or faithful-family
membership is assumed for the particular U or K.

Source: Aschbacher–Smith, 13.3.2(3), p.885; 13.3.14, pp.891–893;
14.5.21(2), p.1019, used in 14.7.70–71, pp.1074–1075.
-/

public section
noncomputable section
open Subgroup Representation Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter13.Section03.Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
include d

private theorem U_ne_bot : F.U ≠ ⊥ := by
  intro he
  exact d.z_ne_one (show d.z ∈ (⊥ : Subgroup G) from he ▸ d.U₀_le_U d.z_mem_U₀)

/-- Literal Irr⁺ minimality of the original span for its actual residual actor. -/
theorem U_minimal_noncentral (A : Subgroup G) (hAU : A ≤ F.U)
    (hAn : K F ≤ normalizer (A : Set G)) : A = F.U ∨ A ≤ centralizer (K F : Set G) := by
  let b := d.KNaturalSection d.U_eq_commutator_K
  by_cases hA0 : A ≤ d.U₀
  · exact Or.inr (hA0.trans (le_centralizer_iff.mp d.K_centralizes_U₀))
  · left
    obtain ⟨a, ha, ha0⟩ := SetLike.not_le_iff_exists.mp hA0
    let aU : F.U := ⟨a, hAU ha⟩
    have hpa : (b.coordinates aU).toAdd ≠ 0 := by
      intro he
      exact ha0 ((b.coordinates_eq_one_iff aU).mp he)
    have hsup : F.U ≤ A ⊔ d.U₀ := by
      intro v hv
      let vU : F.U := ⟨v, hv⟩
      by_cases hpv : (b.coordinates vU).toAdd = 0
      · exact mem_sup_right ((b.coordinates_eq_one_iff vU).mp hpv)
      · obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero
          (b.coordinates aU).toAdd (b.coordinates vU).toAdd hpa hpv
        obtain ⟨k, hk⟩ := d.KSL2FourMap_surjective g
        let a' : F.U := ⟨(k : G) * a * (k : G)⁻¹,
          (mem_normalizer_iff.mp (b.normalized k.property) a).mp aU.property⟩
        have ha' : (a' : G) ∈ A := (mem_normalizer_iff.mp (hAn k.property) a).mp ha
        have hp : b.coordinates a' = b.coordinates vU := by
          apply Multiplicative.toAdd.injective
          exact (b.equivariant k aU).trans (by
            change SL2FourNatural.action (d.KSL2FourMap k) _ = _
            rw [hk]
            exact hg)
        have hz : (a'⁻¹ * vU : F.U).val ∈ d.U₀ := (b.coordinates_eq_one_iff _).mp (by
          rw [map_mul, map_inv, hp, inv_mul_cancel])
        have hm : (a' * (a'⁻¹ * vU) : F.U).val ∈ A ⊔ d.U₀ :=
          mul_mem (mem_sup_left ha') (mem_sup_right hz)
        simpa only [mul_inv_cancel_left] using hm
    apply le_antisymm hAU
    rw [d.U_eq_commutator_K]
    apply (commutator_mono hsup le_rfl).trans
    have hec : ⁅K F, A⁆ = ⁅K F, A ⊔ d.U₀⁆ :=
      commutator_eq_of_centralizing_sup (sup_comm d.U₀ A)
        (le_centralizer_iff.mp d.K_centralizes_U₀)
        ((hAU.trans d.U_le_K).trans (K F).le_normalizer)
    rw [commutator_comm (A ⊔ d.U₀), ← hec, commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hAn

/-- The contrary plane centrality puts the entire original span in the core center. -/
theorem U_le_omegaCenter_of_plane_centralized
    (hplane : F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    F.U ≤ omegaOneCenterAmbient (F.H.pCoreIn 2) := by
  let := d.natural.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    have hcard := F.card 1 (by decide)
    simp [he] at hcard
  have hpointp : IsPGroup 2 (F.Vi 1) :=
    T.isPGroup'.to_le ((F.le_seed 1).trans d.natural.chosen.le_sylow)
  have hH : F.H ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T
      (d.counterexample.qtke.toIsQTKE.evenCharacteristic T)
      ⟨F.Vi 1, hp, hpointp, rfl⟩ (F.invariant 1)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  let := IsElementaryAbelian.of_surjective (p := 2)
    (F.tildeMap V hVH) (F.tildeMap_surjective V hVH)
  have hspan : F.Vi 3 = conjugateSpanBy (F.Vi 2) (F.Li L 1) := by
    rw [F.last]
    exact (F.seed_eq_plane_span L (by decide) d.natural.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural d.natural.naturalMarking (by decide))).symm
  have h := (reduction_a (F.Vi 2) (F.Vi 3) (F.Li L 1) F.H
    ((F.le_seed 2).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H))
    ((F.Li_le L 1).trans inf_le_right) hspan hH
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hplane))).2
  simpa only [F.last, InvariantFlag.U, InvariantFlag.UH] using h

/-- Contrary centrality makes the original U a reduced subgroup of H=KT. -/
theorem U_reduced_of_plane_centralized (hc : d.SectionCentralizer)
    (hplane : F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    IsPReduced 2 (F.U.subgroupOf F.H) := by
  let := d.U_elementary
  let := d.natural.chosen.elementary
  have hcore : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
    (pCore 2 F.H).comap_map_eq_self_of_injective F.H.subtype_injective
  let : (F.U.subgroupOf F.H).Normal := normal_subgroupOf_of_le_normalizer d.conjugationSection.normalized
  have he : centralizer (F.U.subgroupOf F.H : Set F.H) = pCore 2 F.H := by
    ext h
    constructor
    · intro hh
      have ha : d.action h = 1 := by
        apply LinearMap.ext
        intro w
        obtain ⟨v, hv⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
        have hx : (⟨h * v * (h : G)⁻¹,
          (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) v).mp v.property⟩ : F.U) = v := by
          apply Subtype.ext
          have hm := congrArg Subtype.val (hh ⟨v, F.U_le_H v.property⟩ v.property)
          change (v : G) * h = h * v at hm
          change (h : G) * v * (h : G)⁻¹ = v
          rw [← hm, mul_inv_cancel_right]
        have heq := d.conjugationSection.equivariant h v
        rw [hx, hv] at heq
        exact heq.symm
      have hk : h ∈ d.action.ker := ha
      rw [hc, hcore] at hk
      exact hk
    · intro hh v hv
      apply Subtype.ext
      have hu := d.U_le_omegaCenter_of_plane_centralized hplane hv
      exact (((mem_omegaOneCenterAmbient_iff _ _).mp hu).2.2 h
        (mem_map_of_mem F.H.subtype hh)).symm
  refine ⟨inferInstance, ?_, ?_⟩
  · exact IsElementaryAbelian.of_surjective
      (subgroupOfEquivOfLe (d.conjugationSection.section_le)).symm.toMonoidHom
      (subgroupOfEquivOfLe (d.conjugationSection.section_le)).symm.surjective
  · let e := QuotientGroup.quotientMulEquivOfEq he
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    exact (pCore_map_iso 2 e).trans (pCore_quotient_pCore_eq_bot 2)

/-- In the contrary case K belongs to the original faithful local family. -/
theorem K_faithful_of_plane_centralized
    (hplane : F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    K F ∈ MainForward.faithfulLocalComponents T := by
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (d.counterexample.qtke.toIsQTKE.evenCharacteristic T)).mpr
  refine ⟨d.K_mem_localFamily, ?_⟩
  have hUQ := d.U_le_K_core
  have hQH : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)
  have hUC : F.U ≤ omegaOneCenterAmbient ((K F).pCoreIn 2) := by
    intro u hu
    obtain ⟨_, hp, hcent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp
      (d.U_le_omegaCenter_of_plane_centralized hplane hu)
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUQ hu, hp, fun q hq => hcent q (hQH hq)⟩
  have hUm : F.U ≤ ChapterA.Section04.intrinsicSignalizerModule (K F) := by
    calc
      F.U = ⁅F.U, K F⁆ := d.U_eq_commutator_K
      _ ≤ ⁅omegaOneCenterAmbient ((K F).pCoreIn 2), K F⁆ := commutator_mono hUC le_rfl
      _ = _ := by rw [ChapterA.Section04.intrinsicSignalizerModule,
        ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]; rfl
  intro he
  exact d.U_ne_bot (bot_unique (he ▸ hUm))

/-- The contrary assumption produces a source choice on the same subgroup U. -/
theorem U_chosen_of_plane_centralized (hc : d.SectionCentralizer)
    (hplane : F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    Nonempty (Chapter12.Section02.ChosenModule T (K F) F.U) := by
  apply Chapter13.Section03.PlaneNoncentralitySource.exists_chosenModuleOfMinimal
  · rw [← d.residual_product]
    exact d.U_reduced_of_plane_centralized hc hplane
  · rw [← d.residual_product]
    exact d.conjugationSection.section_le
  · exact (F.invariant 1).trans (H_normalizes_K F)
  · rw [← d.residual_product]
    exact d.conjugationSection.normalized
  · exact d.U_eq_commutator_K.symm
  · exact d.U_ne_bot
  · exact d.U_minimal_noncentral

/-- The actual Chapter 14 specialization of 13.3.14, using only the earlier
universal 13.3.2(3) module alternative beyond the existing source data. -/
theorem plane_noncentrality_of_source1332
    (earlier : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hc : d.SectionCentralizer) :
    ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hplane
  obtain ⟨chosen⟩ := d.U_chosen_of_plane_centralized hc hplane
  have hmodel := earlier G T L d.counterexample (K F)
    (d.K_faithful_of_plane_centralized hplane) ⟨d.K_quotient_equiv_A5⟩ F.U chosen
  have hcard := Chapter13.Section03.PlaneNoncentralitySource.alternatingFive_model_card hmodel
  have hsection := (d.KNaturalSection d.U_eq_commutator_K).card_section
  have hnatural : Nat.card SL2FourNatural.V = 16 := by
    rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]
  rw [hnatural, hcard] at hsection
  have hpoint : 2 ≤ Nat.card d.U₀ := by
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion d.point_le_U₀)
      (Subgroup.inclusion_injective d.point_le_U₀)
    rwa [show Nat.card (F.Vi 1) = 2 from by simpa using F.card 1 (by decide)] at h
  omega

/-- Discharge the original point-commutator premise of 14.7.70 and 14.7.71. -/
theorem U_core_commutator_eq_point_of_source1332
    (earlier : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hc := d.sectionCentralizer_of_earlier_setup structural uniqueness
  exact d.U_core_commutator_eq_point_of_plane_moved hc
    (d.plane_noncentrality_of_source1332 earlier hc)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
