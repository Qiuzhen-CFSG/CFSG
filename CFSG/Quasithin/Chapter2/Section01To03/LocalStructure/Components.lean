module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Control
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CComponent.CentralInvolution

/-!
# Inversion and ordinary component embeddings in Γ₀

Source: Aschbacher–Smith 2.3.9(5–6), printed pp.525–526.
The genuine earlier universal implications 1.1.5(2–3) and 1.2.4 remain
explicit inputs, with producers qt-1-01 and qt-1-02-adequate-assembly.
The local hypotheses for both H and N_G(O₂(H)) are constructed here.
An ordinary component of H belongs to the actual local C-component family
in that normalizer. The 1.2.4 witness is initially only a C-component;
the proved A.3.3 commutator and Fitting-centralizer arguments promote it
to an ordinary component. The original involution and literal embeddings
are preserved throughout. No component-list refinement is asserted.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

/-- Exactly the structural clauses of the earlier universal 1.1.5.
No Γ condition, normalizer-component embedding, or refined model list
is included. The model/action clauses are supplied separately to refinement. -/
def Structural115Input (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H S M z →
      (∀ x ∈ (pPrimeCore 2 H).map H.subtype, z * x * z⁻¹ = x⁻¹) ∧
      ∀ B : Subgroup H, IsComponent H B →
        B.map H.subtype = ⁅B.map H.subtype, zpowers z⁆ ∧
        ¬ B.map H.subtype ≤ M ∧ z ∈ normalizer (B.map H.subtype : Set G)

/-- The containment clause of earlier source 1.2.4, expressed in one
ambient group. L is the actual three-condition local C-component family. -/
def Embedding124Input (G : Type*) [Group G] : Prop :=
  ∀ (N : Subgroup G), N ∈ Chapter1.H G → ∀ (P : Sylow 2 N) (B : Subgroup G),
    B ≤ N → B ∈ Chapter1.L G ((P : Subgroup N).map N.subtype) →
      ∃ D : Subgroup N, D.IsCComponent ∧ B ≤ D.map N.subtype

/-- Lemma 2.3.9(5), from the earlier universal 1.1.5 implication. -/
theorem lemma_2_3_9_5_of_115 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source : Structural115Input G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x) :
    centralizer ({z} : Set G) ≤ M ∧
      ∀ x ∈ (pPrimeCore 2 H).map H.subtype, z * x * z⁻¹ = x⁻¹ := by
  have hh := lemma_2_3_8_6 hG T hM hTM hunique hH hpair S hUS hz hzS hcentral hMcentral
  exact ⟨hh.centralizer_le, (source H S M z hh).1⟩

/-- Lemma 2.3.9(6), including promotion of the containing C-component
to an ordinary component of the literal core normalizer. -/
theorem lemma_2_3_9_6_of_115_124 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (source124 : Embedding124Input G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x)
    (B : Subgroup H) (hB : IsComponent H B) :
    B.map H.subtype = ⁅B.map H.subtype, zpowers z⁆ ∧ ¬ B.map H.subtype ≤ M ∧
      ∃ D : Subgroup (normalizer (twoCore H : Set G)),
        IsComponent (normalizer (twoCore H : Set G)) D ∧
        B.map H.subtype ≤ D.map (normalizer (twoCore H : Set G)).subtype := by
  have hh := lemma_2_3_8_6 hG T hM hTM hunique hH hpair S hUS hz hzS hcentral hMcentral
  obtain ⟨hmoved, hout, _⟩ := (source115 H S M z hh).2 B hB
  refine ⟨hmoved, hout, ?_⟩
  let N := normalizer (twoCore H : Set G)
  let A := B.map H.subtype
  have hAN : A ≤ N := (map_subtype_le _).trans (le_normalizer_twoCore H)
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  have hn := lemma_2_3_9_1 hH hpair S hUS
  obtain ⟨P, hP⟩ := hn.2.1
  have hNgam := (lemma_2_3_8_3 hgam hpair).2
  have hNpair := (lemma_2_3_8_3 hgam hpair).1
  have hAcomp : (A.subgroupOf H).IsCComponent := by
    change ((B.map H.subtype).comap H.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact hB.isCComponent
  have hAlocal : A ∈ Chapter1.L G ((P : Subgroup N).map N.subtype) := by
    rw [hP]
    exact Chapter1.mem_L_of_cComponent hgam.1 ⟨S, rfl⟩ (map_subtype_le _) hAcomp
  obtain ⟨D, hD, hAD⟩ := source124 N hNgam.1 P A hAN hAlocal
  have hNz : z ∈ N := (map_subtype_le _).trans (le_normalizer_twoCore H) hzS
  let zN : N := ⟨z, hNz⟩
  have hNS : Chapter1.Lemma115Hypotheses N P M z :=
    lemma_2_3_8_6 hG T hM hTM hunique hn.1 hNpair P (hP.symm ▸ hUS)
      hz (hP.symm ▸ hzS) (hP.symm ▸ hcentral) hMcentral
  have hinv := (source115 N P M z hNS).1
  have hAnonsolv : ¬ Group.IsSolvable (A.subgroupOf N) := by
    intro hs
    let := hs
    let e := (subgroupOfEquivOfLe hAN).trans (B.equivMapOfInjective H.subtype H.subtype_injective).symm
    exact hB.isCComponent.not_isSolvable
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hAD' : A.subgroupOf N ≤ D := by
    intro x hx
    obtain ⟨d, hd, he⟩ := hAD hx
    exact (Subtype.ext he : d = x) ▸ hd
  have hmoveN : A.subgroupOf N = ⁅A.subgroupOf N, zpowers zN⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hAN, MonoidHom.map_zpowers]
    exact hmoved
  refine ⟨D, component_of_moved_subgroup hD hAD' hAnonsolv zN hmoveN ?_ ?_, hAD⟩
  · intro b hb
    apply Subtype.ext
    exact hcentral b (hP ▸ pCoreIn_le_sylow N P (mem_map_of_mem N.subtype hb))
  · intro b hb
    apply Subtype.ext
    exact hinv b (mem_map_of_mem N.subtype hb)

/-- Assemble the exact common local input used by component refinement.
The component-list and model-action conclusions of 1.1.5 remain separate. -/
theorem componentRefinement_localSetup_of_sources {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x)
    (B : Subgroup H) (hB : IsComponent H B) :
    ComponentRefinement.LocalSetup H (B.map H.subtype) M S z := by
  have hh := lemma_2_3_8_6 hG T hM hTM hunique hH hpair S hUS hz hzS hcentral hMcentral
  obtain ⟨hmoved, hout, hnorm⟩ := (source115 H S M z hh).2 B hB
  refine ⟨inferInstance, map_subtype_le _, ?_, hh.mem_HeOver.2.2,
    lemma_2_3_9_4 hh.mem_HeOver.1 hH hpair S hUS, hh.mem_HeOver.1,
    hz, hzS, hcentral, hnorm, hh.centralizer_le, hmoved, hout,
    localBlockGeneration_of_localC129 hG sourceC T hTM hunique hH hpair S hUS _⟩
  change IsComponent H ((B.map H.subtype).comap H.subtype)
  rwa [comap_map_eq_self_of_injective H.subtype_injective]

end CFSG.Quasithin.Chapter2
