module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BinaryCorank
public import Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.Overgroups

/-!
# The binary component's actual local intersection

The source Sylow subgroup lies in L ∩ M. In A₆, every proper overgroup of
that Sylow subgroup is either the Sylow subgroup itself or a maximal
parabolic. Its prime-to-two residual is the whole intersection. Applying
the source residual containment therefore identifies L ∩ M with C_L(V).

The Borel assertion uses the literal preimage of the Sylow normalizer in
L/Z(L). No parabolic-action conclusion is used here.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem binary_sylow_le_intersection (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ S : Sylow 2 L, (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  refine ⟨S, ?_⟩
  intro x hx
  have hxQ := (hS ▸ mem_map_of_mem L.subtype hx).2
  exact ⟨x.property, h.sylow_le hxQ.1⟩

/-- The residual here is computed inside the actual L ∩ M. -/
theorem binary_intersection_residual_eq_top (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    primeToResidual 2 ↥(L ⊓ M) = ⊤ := by
  obtain ⟨e⟩ := alternating_six_of_model_one hm
  obtain ⟨S, hS⟩ := binary_sylow_le_intersection h hU hL
  have hr := sylow_overgroup_residual e S ((L ⊓ M).subgroupOf L) hS
  let f := subgroupOfEquivOfLe (show L ⊓ M ≤ L from inf_le_left)
  rw [← map_primeToResidual f, hr, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr f.surjective]

/-- The source normalizer containment and residual condition identify the
local intersection with the literal V-centralizer in L. -/
theorem binary_intersection_eq_centralizer (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    L ⊓ M = L ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · have hr := component_intersection_residual hU hL.1
    rw [binary_intersection_residual_eq_top h hU hL hm, ← MonoidHom.range_eq_map, range_subtype] at hr
    exact hr
  · exact inf_le_inf_left L ((Subgroup.centralizer_le_normalizer _).trans h.normalizer_le)

omit [Finite G] in
private theorem binary_center_eq_bot (e : L ≃* alternatingGroup (Fin 6)) :
    center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hy := (centerCongr e ⟨x, hx⟩).property
  change e x ∈ center (alternatingGroup (Fin 6)) at hy
  rw [alternatingGroup.center_eq_bot (by simp)] at hy
  exact mem_bot.mpr (e.injective ((mem_bot.mp hy).trans (map_one e).symm))

private theorem binary_borel_of_normalizer (hc : center L = ⊥)
    (S : Sylow 2 L) (hB : (L ⊓ M).subgroupOf L = normalizer (S : Set L)) :
    BorelPreimage L (L ⊓ M) := by
  let q := QuotientGroup.mk' (center L)
  have hq : Function.Bijective q := by
    refine ⟨(MonoidHom.ker_eq_bot_iff q).mp ?_, QuotientGroup.mk'_surjective _⟩
    rw [QuotientGroup.ker_mk', hc]
  let R := S.mapSurjective (f := q) hq.2
  refine ⟨inf_le_left, R, ?_⟩
  change (L ⊓ M).subgroupOf L =
    (normalizer ((S : Subgroup L).map q : Set _)).comap q
  rw [← map_normalizer_eq_of_bijective _ hq, comap_map_eq_self_of_injective hq.1]
  exact hB

/-- The source binary intersection is either a Borel or a maximal parabolic.
The source Sylow arrangement already supplies the required containment. -/
theorem binary_intersection_cases (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    BorelPreimage L (L ⊓ M) ∨ MaximalParabolic L (L ⊓ M) := by
  obtain ⟨e⟩ := alternating_six_of_model_one hm
  obtain ⟨S, hS⟩ := binary_sylow_le_intersection h hU hL
  have hn : (L ⊓ M).subgroupOf L ≠ ⊤ := by
    intro he
    apply component_not_le h earlier hU hL
    intro x hx
    have hh : (⟨x, hx⟩ : L) ∈ (L ⊓ M).subgroupOf L := he.symm ▸ mem_top _
    exact hh.2
  rcases sylow_overgroup_cases e S ((L ⊓ M).subgroupOf L) hS hn with he | hc
  · exact Or.inl (binary_borel_of_normalizer (binary_center_eq_bot e) S
      (he.trans (normalizer_sylow e S).symm))
  · exact Or.inr ⟨inf_le_left, hc, S, (normalizer_sylow e S).symm ▸ hS⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
