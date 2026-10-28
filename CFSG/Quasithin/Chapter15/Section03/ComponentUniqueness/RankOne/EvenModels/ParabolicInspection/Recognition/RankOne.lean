module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import CFSG.Quasithin.MainConverse.RankOneLocal

/-!
# Recognition for the linear and unitary rank-one components

Every proper overgroup of a component Sylow subgroup lies in its Borel.
This provides the invariant hull. The Borel is maximal two-local, so the
proved even-characteristic calculation for the actual PSL₂ or PSU₃ model
supplies its self-centralizing two-core. The extension argument then uses
the maximality of the original local subgroup in the action quotient.

Simplicity and nonabelianity are inherited from the incoming component.
The unitary field order is the fixed-field order. Source: Aschbacher--Smith,
F.1.3(1), pp.259--260, and 15.3.43, p.1140.
-/

public section

open Subgroup CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {H : Type*} [Group H]

private theorem proper_overgroup_le_borel (K S : Subgroup H) (T : Sylow 2 K)
    (hT : (T : Subgroup K).map K.subtype = S ⊓ K) (hf : RankOneSylowFacts T)
    (Q : Subgroup H) (hSQ : S ⊓ K ≤ Q) (hQK : Q < K) : Q ≤ borel K S := by
  have hQT : Q.subgroupOf K < ⊤ := by
    apply (map_lt_map_iff_of_injective K.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hQK.le, ← MonoidHom.range_eq_map,
      range_subtype] using hQK
  have hTQ : (T : Subgroup K) ≤ Q.subgroupOf K := by
    intro x hx
    apply hSQ
    rw [← hT]
    exact mem_map_of_mem K.subtype hx
  have hQB := hf.unique_maximal (Q.subgroupOf K) hTQ hQT
  change Q.subgroupOf K ≤ sylowNormalizer T at hQB
  rw [← borel_subgroupOf_eq_sylowNormalizer K S T hT] at hQB
  intro x hx
  exact hQB (show (⟨x, hQK.le hx⟩ : K) ∈ Q.subgroupOf K from hx)

/-- The rank-one Borel is maximal among actual two-locals, so the source's
even-characteristic hypothesis applies to it. -/
private theorem rankOne_normalizer_core {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hna : ¬ IsMulCommutative K) (he : IsEvenCharacteristic K)
    (T : Sylow 2 K) (hf : RankOneSylowFacts T) :
    centralizer (pCore 2 (sylowNormalizer T) : Set (sylowNormalizer T)) ≤
      pCore 2 (sylowNormalizer T) := by
  have hTne : (T : Subgroup K) ≠ ⊥ := by
    intro hz
    have hp := hf.proper
    change normalizer ((T : Subgroup K) : Set K) < ⊤ at hp
    rw [hz, normalizer_eq_top] at hp
    exact hp.false
  apply he T (sylowNormalizer T) ?_ (T : Subgroup K).le_normalizer
  refine ⟨⟨T, hTne, T.isPGroup', rfl⟩, ?_⟩
  intro U hU hNU
  exact hf.unique_maximal U ((T : Subgroup K).le_normalizer.trans hNU)
    (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hU))

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

private theorem rankOne_geometry
    (he : IsEvenCharacteristic (c.toComponentAction.image L))
    (hf : ∀ T : Sylow 2 (c.toComponentAction.image L), RankOneSylowFacts T) :
    InvariantHull (c.toComponentAction.image L) (c.toComponentAction.image S)
      (c.toComponentAction.image M) ∧
    ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  let K := c.toComponentAction.image L
  let S' := c.toComponentAction.image S
  let N := c.toComponentAction.image M
  let B := borel K S'
  let : IsSimpleGroup K := c.quotient.simple
  obtain ⟨T, hT⟩ := quotient_component_sylow c
  have hS' : S' ≤ N := map_mono (fun _ hx => c.sylow_le_M hx)
  have hB : B < K := by
    have h := (map_lt_map_iff_of_injective K.subtype_injective).mpr (hf T).proper
    change (sylowNormalizer T).map K.subtype < (⊤ : Subgroup K).map K.subtype at h
    rw [← borel_subgroupOf_eq_sylowNormalizer K S' T hT,
      map_subgroupOf_eq_of_le (borel_le K S'), ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hn : S' ≤ normalizer (B : Set c.toComponentAction.Quotient) := by
    have hK : S' ≤ normalizer (K : Set c.toComponentAction.Quotient) := by
      rw [normalizer_eq_top]
      exact le_top
    exact (le_inf hK
      (((le_inf S'.le_normalizer hK).trans inf_normalizer_le_normalizer_inf).trans
        (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hcore : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (borelNormalizerEquiv K S' T hT)).mpr
      (rankOne_normalizer_core (quotient_component_nonabelian c) he T (hf T))
  refine ⟨⟨B, le_rfl, hB, hn, ?_⟩, ?_⟩
  · exact proper_overgroup_le_borel K S' T hT (hf T) (N ⊓ K)
      (inf_le_inf_right K hS') (quotient_intersection_proper c)
  · intro Q hBQ hQK _
    have hQB := proper_overgroup_le_borel K S' T hT (hf T) Q
      ((localSylow_le_borel K S').trans hBQ) hQK
    have hQB' : Q = B := le_antisymm hQB hBQ
    subst Q
    exact hcore

/-- Recognition of the actual local intersection for every larger-field PSL₂ model. -/
theorem quotientParabolic_linear {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (c.toComponentAction.image L) 2 (2 ^ n)) :
    QuotientParabolic c := by
  let : IsSimpleGroup (c.toComponentAction.image L) := c.quotient.simple
  have he := MainConverse.psl2_evenCharacteristic (quotient_component_nonabelian c) hn hm
  have hf : ∀ T : Sylow 2 (c.toComponentAction.image L), RankOneSylowFacts T := by
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
    intro T
    apply rankOneSylowFacts_of_equiv T e
    exact rankOneSylowFacts_psl2 F n (by omega) hcard _
  obtain ⟨hh, hc⟩ := rankOne_geometry c he hf
  exact quotientParabolic_of_geometry c hh hc

/-- Recognition of the actual local intersection for every larger-field PSU₃ model. -/
theorem quotientParabolic_unitary {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSU (c.toComponentAction.image L) 3 (2 ^ n)) :
    QuotientParabolic c := by
  let : IsSimpleGroup (c.toComponentAction.image L) := c.quotient.simple
  have he := MainConverse.psu3_evenCharacteristic (quotient_component_nonabelian c) hn hm
  have hf : ∀ T : Sylow 2 (c.toComponentAction.image L), RankOneSylowFacts T := by
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
    intro T
    apply rankOneSylowFacts_of_equiv T e
    exact rankOneSylowFacts_psu3 J n (by omega) hcard hconj _
  obtain ⟨hh, hc⟩ := rankOne_geometry c he hf
  exact quotientParabolic_of_geometry c hh hc

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
