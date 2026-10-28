module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ModelClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.GeneratedSource
/-! Source component selection with the full model input discharged.
For every original Gamma-zero component, choose a local pair, its containing
Sylow, the actual ambient Sylow supplied by 2.3.9, and a central involution.
The complete marked model inspection then supplies the exact four model
families used by finite component descent. Thus original 2.5.3(4) and the
component-generated Gamma-plus construction retain only the genuine earlier
C.1.29 local block theorem; no model selection or descent premise remains.
Source: Aschbacher--Smith 2.5.2--4, printed pp.551--554. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem nonBenderSourceModels
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N=M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) : NonBenderSourceModels M := by
  intro H hH D hD hb
  have hg : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨⟨U,HU⟩,hpair⟩ := hg.2
  have hUH : U ≤ H := hpair.1.2.2.2.1.trans hpair.2
  have hp : IsPGroup 2 (U.subgroupOf H) := hpair.1.1.1.2.comap_subtype
  obtain ⟨S,hUS⟩ := hp.exists_le_sylow
  have hUSG : U ≤ (S : Subgroup H).map H.subtype := by
    intro u hu
    exact ⟨⟨u,hUH hu⟩,hUS hu,rfl⟩
  obtain ⟨T,hTM,hST,hZS,_⟩ := lemma_2_3_9_3 T₀ hT₀M hunique
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hT₀M)) hH hpair S hUSG
  have hTne : (T : Subgroup G)≠⊥ := ne_of_gt (lt_of_le_of_lt bot_le hST)
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr hTne
  let : Nontrivial (center T) := T.isPGroup'.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center T) := by
    rcases (T.isPGroup'.to_subgroup (center T)).card_eq_or_dvd with he | he
    · have := Finite.one_lt_card (α := center T)
      omega
    · exact he
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center T) 2 hdiv
  have hzi : orderOf ((z : T) : G)=2 :=
    (Subgroup.orderOf_coe (z : T)).trans ((Subgroup.orderOf_coe z).trans hz)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N=M := by
    intro N hN hTN
    have hNM : N ≤ M := by
      apply core_overgroup_le_of_sylow T₀ hT₀M hunique
        (Chapter1.mem_H_of_isTwoLocal hN.1) (T.subtype hTM)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hTN
    exact le_antisymm hNM (hN.2 hM.1 hNM)
  let L := D.map H.subtype
  have hLc : IsComponent H (L.subgroupOf H) := by
    change IsComponent H ((D.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  let c : MathieuSourceSetup H L M S ((z : T) : G) :=
    ⟨T,hM,hTM,huniq,hH,U,HU,hpair,hUSG,map_subtype_le D,hLc,hST,hZS,
      mem_map_of_mem (T : Subgroup G).subtype z.property,hzi⟩
  let e := D.equivMapOfInjective H.subtype H.subtype_injective
  have hn : ¬ ClassificationModels.IsBenderModel L := fun h => hb (h.of_mulEquiv e)
  rcases MathieuSourceSetup.nonBender_model c hG sourceC hempty hn with hm | hm | hm | hm
  · exact .inl (hm.of_mulEquiv e)
  · exact .inr (.inl (hm.of_mulEquiv e))
  · exact .inr (.inr (.inl (hm.imp (fun h => h.map (e.trans ·)) (fun h => h.map (e.trans ·)))))
  · exact .inr (.inr (.inr (hm.of_mulEquiv e)))

variable {H : Subgroup G}

/-- The original selected component, including both starred conditions. -/
theorem lemma_2_5_3_four_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N=M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H=⨅i,normalizer (B i : Set G))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ D : Subgroup H, IsComponent H D ∧ ¬ ClassificationModels.IsBenderModel D ∧
      let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
      X ∈ gammaZero (Chapter1.He G) M ∧
        (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
        (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) :=
  lemma_2_5_3_four_of_source_models hG T₀ hM hT₀M hunique hH hempty
    (nonBenderSourceModels hG sourceC T₀ hM hT₀M hunique hempty) B hp hBH hHnorm S hSM

/-- Construct the original component-generated group from any Gamma-zero
source group and its prescribed Sylow. The model and normalizer-presentation
inputs of the earlier conditional construction are discharged. -/
theorem exists_component_generated_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N=M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ X K : Subgroup G,
      X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      IsComponentIn K X ∧ ¬ ClassificationModels.IsBenderModel K ∧
      Chapter1.IsSylowIn 2 ((S : Subgroup H).map H.subtype) X ∧
      Chapter1.IsSylowIn 2 ((S : Subgroup H).map H.subtype) (X ⊓ M) ∧
      X=K ⊔ (S : Subgroup H).map H.subtype :=
  exists_component_generated_source_of_models hG T₀ hM hT₀M hunique hH hempty
    (nonBenderSourceModels hG sourceC T₀ hM hT₀M hunique hempty) S hSM

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
