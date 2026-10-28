module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.ResidualGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.NaturalBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.PrimeActor

/-!
# Source-correct constrained rank-one reductions

The original prime actor and the full A₅-block automorphism calculation
exclude the exceptional permutation block, for p=3 or5, before exchanged
selection. Thus only the genuine natural L₂(2ⁿ) block remains. In particular
the natural L₂(4) block is not discarded as an A₅ permutation module.

The residual-geometry assembly uses O²(B) in its exceptional contract and
constructs its own actor. Natural-block Borel perfectness, centralizer
comparison and Thompson normalization are proved on the full cover,
including the field-four natural block. The original earlier15.1.14
input in PreExclusionSource retains its separate producer and final discharge
at the pre-exclusion catalogue and large-action-exclusion owners.

Source: Aschbacher--Smith15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The exceptional A₅ permutation block is excluded on the original source,
with its constructed prime actor and no local model-action callback. -/
theorem PreExclusionSource.false_of_constrained_alternatingFive
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hb : ChapterC.IsAlternatingBlock d.L 5)
    (hmove : ⁅d.L, elementaryAbelianMaxJ d.S⁆ = d.L) : False := by
  obtain ⟨Y,hY,_⟩ := s.rankOne_prime_actor (h := h) hG hM hJ
  exact s.false_of_moving_actor_centralizes (h := h)
    (s.alternatingFive_primeActor_centralizes (h := h) hp hG hM hJ hb hmove hY) hY.moves

/-- The surviving rank-one row is the natural block, including n=2. -/
theorem PreExclusionSource.constrained_rankOne_is_natural
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (r : d.ConstrainedRankOneAlternative) : ∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n := by
  rcases r.block with hn | hb
  · exact hn
  · exact (s.false_of_constrained_alternatingFive (h := h) hp hG hM hJ hb r.thompson).elim

/-- Corrected residual-based conditional assembly. The constructed actor
discharges the exceptional action on the original source. -/
theorem PreExclusionSource.no_constrained_rankOne_of_residual_geometry
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hgeometry : d.ConstrainedRankOneAlternative →
      d.RankOneBorelGeometry ∨ d.RankOneExceptionalResidualGeometry) :
    ¬ d.ConstrainedRankOneAlternative := by
  intro r
  rcases hgeometry r with hB | hE
  · have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    have hn := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
    exact s.false_of_thompson_borel (h := h) hM.1.2 he hn hB.perfect
      (s.rankOneBorelClosure_le (h := h)) hB.thompson hB.centralizers
  · exact s.false_of_constrained_alternatingFive (h := h) hp hG hM hJ hE.block r.thompson

/-- Adapter assembling the source contradiction from natural-block Borel
geometry and the proved exceptional action. -/
theorem PreExclusionSource.no_constrained_rankOne_of_natural_borel
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hgeometry : d.ConstrainedRankOneAlternative →
      (∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n) → d.RankOneBorelGeometry) :
    ¬ d.ConstrainedRankOneAlternative :=
  s.no_constrained_rankOne_of_residual_geometry (h := h) hp hG hM hJ (fun r =>
    Or.inl (hgeometry r (s.constrained_rankOne_is_natural (h := h) hp hG hM hJ r)))

/-- Original15.1.21 constrained rank-one exclusion, before exchanged selection.
The natural block uses the actual orbit Borel, and the exceptional permutation
block uses the constructed noncentral prime actor. No model callback remains. -/
theorem PreExclusionSource.no_constrained_rankOne
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ¬ d.ConstrainedRankOneAlternative := by
  apply s.no_constrained_rankOne_of_natural_borel (h := h) hp hG hM hJ
  intro r hn
  obtain ⟨n,hb⟩ := hn
  exact s.rankOne_natural_borel_geometry (h := h) r hb

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
