module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract
public import Theory.GroupTheory.CComponent.LayerTransport

/-!
# Inputs to the component-model comparison in 1.3.8

An overgroup outside M gives a C-component and the two surviving 1.3.4
alternatives. Its Sylow subgroup is the restriction of the ambient Sylow
subgroup. The characteristic-normalizer argument constructs C.2.3, and the
global He bridge gives F*(K) = O₂(K).

These facts alone do not establish the hypotheses of C.2.7: the chosen
component must also lie outside M and be normalized by R = O₂(XT).
The latter condition is proved in the `Normalization` extension.
`PushingUpComponent` keeps those two additional obligations explicit, without
assuming any pushing-up model or block conclusion. The original overgroup's
noncontainment in M is also an explicit premise of the candidate construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.513–514; Hypothesis C.2.3 and
Lemma C.2.7, printed pp.144–145.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding

universe u
variable {G : Type u} [Group G]

/-- The actual embedding candidate, before proving its two remaining C.2.7
hypotheses. This record contains no pushing-up model or block conclusion. -/
structure ComponentCandidate (κ : GroupClass.{u}) (p : ℕ)
    (T X P M H₀ K : Subgroup G) : Prop where
  overgroup : H₀ ∈ HOver G (T : Set G)
  local_input : LocalInput p T X P H₀
  sylow_two : IsSylowIn 2 T H₀
  component : K ∈ cComponentsIn H₀
  quasisimple : IsQuasisimple (XiQuotient K)
  containment : X ≤ componentOrbit K T
  alternatives : SurvivingAlternatives p T P K
  setup : PushingUpSetup κ H₀ ((X ⊔ T).pCoreIn 2) (H₀ ⊓ M)
  fitting : generalizedFitting K = pCore 2 K

/-- The full component input to C.2.7. The outside condition concerns M_H,
and normalization concerns the actual ambient image of O₂(XT). -/
structure PushingUpComponent (κ : GroupClass.{u}) (p : ℕ)
    (T X P M H₀ K : Subgroup G) : Prop
    extends ComponentCandidate κ p T X P M H₀ K where
  outside : ¬ K ≤ H₀ ⊓ M
  radical_normalizes : (X ⊔ T).pCoreIn 2 ≤ normalizer K

/-- Restrict the ambient Sylow subgroup, construct C.2.3, and use the global
He bridge on the selected C-component. This theorem does not establish
the outside-M premise supplied to it. -/
theorem Configuration.exists_componentCandidate [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G)
    {p : ℕ} {X P L₀ M H₀ : Subgroup G}
    (h : Configuration p T X P L₀ M) (h134 : Source134 κ G)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (hH : H₀ ∈ HOver G (T : Set G))
    (hXH : X ⊔ (T : Subgroup G) ≤ H₀) (hout : ¬ H₀ ≤ M) :
    ∃ K : Subgroup G, ComponentCandidate κ p T X P M H₀ K := by
  have hTH : (T : Subgroup G) ≤ H₀ := hH.2
  have hsyl : IsSylowIn 2 (T : Subgroup G) H₀ :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  have hsqtk := sqtk_of_mem_H hG hH.1
  obtain ⟨K, hK, hq, hXK, ha⟩ :=
    embedding_outside_normalizer h134 h hsqtk hsyl hXH hout
  let _ : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S, hS⟩ := h.sylow
  have hinput : LocalInput p T X P H₀ := by
    simpa only [hS] using localInput_of_mem_Xi h.xi hsyl hXH h.odd h.quotient S
  exact ⟨K, ⟨hH, hinput, hsyl, hK, hq, hXK, ha,
    h.pushingUp_setup T hsqtk hXH, component_fitting_of_global_He h114 hH hK⟩⟩

/-- The relative outside condition of C.2.7 agrees with outside M for
a component already contained in H. -/
theorem ComponentCandidate.outside_iff {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G} (h : ComponentCandidate κ p T X P M H₀ K) :
    (¬ K ≤ H₀ ⊓ M) ↔ ¬ K ≤ M := by
  simp only [le_inf_iff, h.component.1, true_and]

/-- X normalizes the chosen component because it lies in the T-orbit,
and every C-component is normal in the C-component layer of H. -/
theorem ComponentCandidate.xi_normalizes [Finite G] {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G} (h : ComponentCandidate κ p T X P M H₀ K) :
    X ≤ normalizer K := by
  let D := (cComponentLayer H₀).map H₀.subtype
  let _ := cComponentLayer_characteristic (G := H₀)
  have hKD : K ≤ D := by
    simpa only [map_subgroupOf_eq_of_le h.component.1] using
      map_mono (f := H₀.subtype) (le_cComponentLayer h.component.2)
  have hTD : T ≤ normalizer (D : Set G) :=
    h.overgroup.2.trans (H₀.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H₀ (cComponentLayer H₀)))
  have hDN : D ≤ normalizer (K : Set G) := by
    have hh := (map_mono (f := H₀.subtype)
      (cComponentLayer_le_normalizer h.component.2)).trans
        ((K.subgroupOf H₀).le_normalizer_map H₀.subtype)
    simpa only [map_subgroupOf_eq_of_le h.component.1] using hh
  exact h.containment.trans
    ((iSup_conjugates_le_of_le_normalizer K T D hKD hTD).trans hDN)

/-- In the T-invariant alternative, the ambient Sylow condition already
gives the normalization required by C.2.7. The swapped case needs a
separate argument. -/
theorem ComponentCandidate.radical_normalizes_of_invariant [Finite G]
    {κ : GroupClass.{u}} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K) (hTK : T ≤ normalizer K) :
    (X ⊔ T).pCoreIn 2 ≤ normalizer K := by
  obtain ⟨S, hS⟩ := h.sylow_two.restrict le_sup_right h.local_input.overgroup
  exact (hS ▸ pCoreIn_le_sylow (X ⊔ T) S).trans hTK

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
