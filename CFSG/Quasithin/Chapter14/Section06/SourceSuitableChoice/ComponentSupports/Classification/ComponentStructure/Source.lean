module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.ComponentStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Residuals

/-!
# The terminal component structure on the original ambient subgroups

Transport the intrinsic rank-two component theorem through Mc's subtype.
This preserves relative normality, the original Sylow T, conjugation by t⁻¹,
and the literal products in the published terminal alternatives. The full
rank-two hypotheses and original 14.6.18 supply the radical and rank bounds.

The individual quotient models of 14.6.20 now suffice for the component
alternatives and for H∞ = O²(H), H = H∞T. Applying the existing structural
consumer also gives M = LT and M ∩ H = T once the seed-quotient centralizer
calculation is supplied. No residual model or component-generation premise
is retained.

Source: Aschbacher--Smith 14.6.21 and 14.6.23(1--2), pp.1037--1038.
The individual model and seed-centralizer premises remain with the assembly
owner qt-e-suitable-component-supports; original 14.6.18 remains with
qt-e-14625-source. These conditional theorems do not assert 14.6.20.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem intrinsic_component_models (H : Subgroup G)
    (hm : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent →
      ComponentQuotientModels K)
    (D : Subgroup H) (hD : D.IsCComponent) : ComponentQuotientModels D := by
  have hc : ((D.map H.subtype).subgroupOf H).IsCComponent := by
    have he : (D.map H.subtype).subgroupOf H = D :=
      comap_map_eq_self_of_injective H.subtype_injective D
    exact he.symm ▸ hD
  exact (hm (D.map H.subtype) (map_subtype_le D) hc).transport
    (equivMapOfInjective D H.subtype H.subtype_injective).symm

private theorem ambient_alternatives (T : Sylow 2 G) (H K : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hR : solvableRadical H = pCore 2 H) (hr : primeRank 3 H ≤ 2)
    (hm : ∀ D : Subgroup H, D.IsCComponent → ComponentQuotientModels D) :
    TerminalComponentAlternatives T H K := by
  let a := subgroupOfEquivOfLe hKH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc := component_models_alternatives hR hr hm (T.subtype hTH) (K.subgroupOf H) hK
  refine ⟨hKH,hK,?_⟩
  rcases hc with ⟨he,hmod⟩ | ⟨hmod,t,ht,hnt,he⟩ | ⟨hmod,D,hD,hne,hKN,hDN,hdmod,he⟩
  · exact Or.inl ⟨(congrArg (map H.subtype) he).trans
      (map_subgroupOf_eq_of_le hKH),hmod.transport a⟩
  · obtain ⟨em⟩ := hmod
    refine Or.inr (Or.inl ⟨⟨aq.symm.trans em⟩,(t : G),ht,?_,?_⟩)
    · intro hnt'
      apply hnt
      rw [←subgroupOf_normalizer_eq hKH]
      exact hnt'
    · have hp := congrArg (Set.image H.subtype) he
      rw [Set.image_mul] at hp
      change ((solvableResidual H).map H.subtype : Set G) =
        (((K.subgroupOf H).map H.subtype : Subgroup G) : Set G) *
        ((((K.subgroupOf H).map (MulAut.conj t⁻¹).toMonoidHom).map H.subtype : Subgroup G) : Set G) at hp
      have hconj : ((K.subgroupOf H).map (MulAut.conj t⁻¹).toMonoidHom).map H.subtype =
          K.map (MulAut.conj (t : G)⁻¹).toMonoidHom := by
        calc
          _ = ((K.subgroupOf H).map H.subtype).map
              (MulAut.conj (t : G)⁻¹).toMonoidHom := by
            rw [map_map,map_map]
            rfl
          _ = _ := by rw [map_subgroupOf_eq_of_le hKH]
      rw [map_subgroupOf_eq_of_le hKH,hconj] at hp
      exact hp
  · obtain ⟨em⟩ := hmod
    let J := D.map H.subtype
    have hJH : J ≤ H := map_subtype_le D
    have hJ : J.subgroupOf H = D := comap_map_eq_self_of_injective H.subtype_injective D
    have hjne : J ≠ K := by
      intro hj
      apply hne
      rw [←hJ,hj]
    obtain ⟨ed⟩ := hdmod
    let b := equivMapOfInjective D H.subtype H.subtype_injective
    let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    refine Or.inr (Or.inr ⟨⟨aq.symm.trans em⟩,J,hJH,hJ.symm ▸ hD,hjne,hKN,
      hJ.symm ▸ hDN,⟨bq.symm.trans ed⟩,?_⟩)
    have hp := congrArg (Set.image H.subtype) he
    rw [Set.image_mul] at hp
    change ((solvableResidual H).map H.subtype : Set G) =
      (((K.subgroupOf H).map H.subtype : Subgroup G) : Set G) * (J : Set G) at hp
    rwa [map_subgroupOf_eq_of_le hKH] at hp

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (hm : ∀ K : Subgroup G, K ≤ Mc → (K.subgroupOf Mc).IsCComponent →
      ComponentQuotientModels K)

include hG hempty hM hunique hmany hcard e hab hsolv hm

/-- The terminal component quotients determine the actual residual quotient and its generators. -/
theorem terminal_residual_models_of_component_models :
    cComponentLayer Mc = solvableResidual Mc ∧
      ResidualQuotientModels (solvableResidual (Mc ⧸ pCore 2 Mc)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hRad := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc hout
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hr : primeRank 3 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  obtain ⟨_,K,_,hK,_⟩ := terminal_exists_component hG T hempty hM hunique hmany hcard e hab hsolv
  exact component_models_residual hRad hr (intrinsic_component_models Mc hm) (K.subgroupOf Mc) hK

/-- Original 14.6.21 follows from the individual quotient models of 14.6.20. -/
theorem terminal_alternatives_of_component_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    TerminalComponentAlternatives T Mc K := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hRad := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc hout
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hr : primeRank 3 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact ambient_alternatives T Mc K hout.1.2 hKM hK hRad hr (intrinsic_component_models Mc hm)

/-- The original H∞ = O²(H) and H = H∞T, with the residual-model premise discharged. -/
theorem terminal_residual_structure_of_component_models :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) :=
  terminal_residual_structure_of_models hG T hempty hM hunique hmany hcard e hab hsolv
    (terminal_residual_models_of_component_models
      hG T hempty hM hunique hmany hcard e hab hsolv hm).2

/-- Apply the full structural consumer, retaining only the individual models and seed centralizer. -/
theorem terminal_structure_of_component_models_and_seed_centralizer
    (hc : SeedQuotientCentralizerBound T M Mc) :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) ∧
      (M : Set G) = (sourceResidual M Mc : Set G) * ((T : Subgroup G) : Set G) ∧
      M ⊓ Mc = (T : Subgroup G) :=
  terminal_structure_of_models_and_seed_centralizer hG T hempty hM hunique hmany hcard e hab hsolv
    (terminal_residual_models_of_component_models
      hG T hempty hM hunique hmany hcard e hab hsolv hm).2 hc

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
