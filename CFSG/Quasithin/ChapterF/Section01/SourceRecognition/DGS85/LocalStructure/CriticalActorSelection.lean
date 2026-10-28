module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargedQuadraticBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCriticalAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# Actual linear quotients at noncommuting critical endpoints

The full critical-center actions have faithful Sylow images and fixed-space
generation. The enlarged-quotient estimates give both lower index bounds;
the original centralizer intersections force the reciprocal bounds to be
sharp. Thus both actual actor quotients are linear, including when the
original catalogue permits a strict PSU₃(2) enlargement.

The application constructs the existing Chapter 7 edge actor data at a
critical endpoint, with the full edge intersection and intrinsic actor
unchanged. `CriticalActorApplication` discharges the full actor catalogue
for critical pairs meeting both vertex orbits and applies the original
b=1 natural-core consumer. The unrestricted enlargement at other vertices
remains a separate source obligation.
Source: DGS, *Groups and Graphs* (1985), 6.1 and 7.1, pp.118--119,126--127,
with the corrected fixed-generation hypothesis in 5.12.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

private theorem actor_image_nontrivial {D : Type*} [Group D] [Finite D]
    (M Q Z A : Subgroup G) (π : M →* D) (hk : π.ker = Q.subgroupOf M)
    (hAM : A ≤ M) (hQC : Q ≤ centralizer (Z : Set G)) (hne : ⁅Z,A⁆ ≠ ⊥) :
    1 < Nat.card ((A.subgroupOf M).map π) := by
  apply ((A.subgroupOf M).map π).one_lt_card_iff_ne_bot.mpr
  intro he
  have hker := (map_eq_bot_iff (A.subgroupOf M)).mp he
  rw [hk] at hker
  apply hne
  rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact hQC (hker (show (⟨a,hAM ha⟩ : M) ∈ A.subgroupOf M from ha))

/-- At every noncommuting critical pair, the actual intrinsic actor quotients
are linear, with no catalogue or order-144 premise. -/
theorem reduced_critical_actor_quotients_linear (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 (2^n)) ∧
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F w ⧸ pCore 2 (graphLocalGroup F w)) 2 (2^n)) := by
  dsimp only [reducedFamily] at *
  let ht := reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F v) := Noncommuting.graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := Noncommuting.graph_Z_elementary ht w
  let M₀ := graphLocalGroup F v
  let M₁ := graphLocalGroup F w
  let : Finite M₀ := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite M₁ := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z F v) := Finite.of_injective (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let : Finite (Z F w) := Finite.of_injective (inclusion (Z_le_stabilizer F w)) (inclusion_injective _)
  let π₀ := QuotientGroup.mk' (pCore 2 M₀)
  let π₁ := QuotientGroup.mk' (pCore 2 M₁)
  let A₀ := ((Z F w).subgroupOf M₀).map π₀
  let A₁ := ((Z F v).subgroupOf M₁).map π₁
  have hi := source_noncommuting_critical_intersections ht
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hc hne
  obtain ⟨σ₀,d₀,_,hg₀,hd₀⟩ := graph_intrinsic_critical_action ht
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hc
  obtain ⟨σ₁,d₁,_,hg₁,hd₁⟩ := graph_intrinsic_critical_action ht
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hi.1
  have h₁₀ : Z F w ≤ M₀ := pGroup_le_sylowGenerated _ _
    (criticalPair_centers F ht.generate hc).1 (IsElementaryAbelian.isPGroup 2 _)
  have h₀₁ : Z F v ≤ M₁ := pGroup_le_sylowGenerated _ _
    (criticalPair_centers F ht.generate hi.1).1 (IsElementaryAbelian.isPGroup 2 _)
  obtain ⟨T₀,hT₀⟩ := ((IsElementaryAbelian.isPGroup 2 (Z F w)).comap_subtype
    (K := M₀)).exists_le_sylow
  obtain ⟨T₁,hT₁⟩ := ((IsElementaryAbelian.isPGroup 2 (Z F v)).comap_subtype
    (K := M₁)).exists_le_sylow
  let S₀ := T₀.mapSurjective (f := π₀) (QuotientGroup.mk'_surjective _)
  let S₁ := T₁.mapSurjective (f := π₁) (QuotientGroup.mk'_surjective _)
  have hk₀ : π₀.ker = (Q F v).subgroupOf M₀ :=
    (QuotientGroup.ker_mk' _).trans (graph_intrinsic_core ht v).symm
  have hk₁ : π₁.ker = (Q F w).subgroupOf M₁ :=
    (QuotientGroup.ker_mk' _).trans (graph_intrinsic_core ht w).symm
  have hq := Noncommuting.critical_sections_quadratic
    (W₀ := Additive (Z F v)) (W₁ := Additive (Z F w)) M₀ M₁ (Z F v) (Z F w) ⊥ ⊥
    σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁
  have hA₀ : 1 < Nat.card A₀ := actor_image_nontrivial M₀ (Q F v) _ _ π₀ hk₀
    h₁₀ (Noncommuting.graph_Q_centralizes_Z ht v) hne
  have hA₁ : 1 < Nat.card A₁ := actor_image_nontrivial M₁ (Q F w) _ _ π₁ hk₁
    h₀₁ (Noncommuting.graph_Q_centralizes_Z ht w) (by rwa [commutator_comm])
  have hb₀ := reduced_graph_quadratic_bounds (W := Additive (Z F v)) h v σ₀ S₀ A₀ (map_mono hT₀) hA₀ hq.1 hg₀ (hd₀ S₀)
  have hb₁ := reduced_graph_quadratic_bounds (W := Additive (Z F w)) h w σ₁ S₁ A₁ (map_mono hT₁) hA₁ hq.2 hg₁ (hd₁ S₁)
  have hr := Noncommuting.reciprocal_section_indices
    (W₀ := Additive (Z F v)) (W₁ := Additive (Z F w)) M₀ M₁ (Q F v) (Q F w) (Z F v) (Z F w) ⊥ ⊥
    σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁ hk₀ hk₁ hi.2.1 hi.2.2 hne hb₀.1 hb₁.1
  exact ⟨hb₀.2 hr.2.2.1.le,hb₁.2 hr.2.2.2.1.le⟩

/-- Apply the selection to the actual Chapter 7 edge actor interface at either
critical endpoint, preserving the intrinsic actor and full edge intersection. -/
theorem reduced_critical_actor_localData (h : HypothesisF11 L S)
    {v w t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (he : (graph F).Adj v t) :
    ∃ d : LocalRankOneData (stabilizer F v) (stabilizer F v ⊓ stabilizer F t),
      d.Pstar = graphLocalGroup F v := by
  obtain ⟨n,hn,hm⟩ := (reduced_critical_actor_quotients_linear h hc hne).1
  exact Noncommuting.graph_actor_localData_exists (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) he (.linear n hn hm)

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
