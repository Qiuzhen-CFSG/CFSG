module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.RankPlacement

/-!
# Original-source consumers of rank-forced same-pair placement

Three-rank at least two, or one literal wreath parabolic, proves placement
for every source parabolic. Combining this with the original plus geometry
establishes (!) for any escaping family whose plus omega-center has order
two. These results cover ordinary and constrained components and both
pre-exclusion primes, without a later exchanged-source hypothesis.

The original marker application also isolates the remaining branch: S
moves L, the three-rank of L is at most one, and every literal parabolic
quotient is S₃. Its placement and the final seven-row exhaustion remain
with qt-e-15122-pre-exclusion-catalogue and the existing model producers.
Source: Aschbacher--Smith 15.1.22(*), (**), (!), printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The escaping-family centralizer conclusion with normalization,
closure minimality and the moving-block exclusion discharged by rank. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_threeRank
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hr : 2 ≤ primeRank 3 d.L) (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_sylow_normalizes (h := h) hG hM hJ hfull hu
    (d.sylow_normalizes_of_threeRank hG h hr) hcard F hF hout

/-- The same actual consumer when one source parabolic has the wreath
quotient. That parabolic need not belong to the escaping family. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_wreath
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (he : Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
      pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ Q ∈ F, ¬ Q ≤ d.ML → Q ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_sylow_normalizes (h := h) hG hM hJ hfull hu
    (hP.sylow_normalizes_of_wreath hG h he) hcard F hF hout

/-- A precise reduction of the full original placement family. The second
branch records what still needs proof; it does not assert placement there. -/
theorem PreExclusionSource.parabolic_placement_or_moved_cubic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∨
      (¬ d.S ≤ normalizer (d.L : Set G)) ∧ primeRank 3 d.L ≤ 1 ∧
        ∀ P ∈ d.sourceParabolics,
          Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
            pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  by_cases hn : d.S ≤ normalizer (d.L : Set G)
  · exact Or.inl (s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hn)
  · exact Or.inr ⟨hn,d.threeRank_le_one_of_sylow_not_normalizes hG h hn,
      fun _ hP => hP.symmetricThree_of_sylow_not_normalizes hG h hn⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The general original marker has the proved rank-two placement and
centralizer conclusions, and an explicit reduction of its remaining branch.
The earlier 15.1.14 residual premise keeps its existing source owner. -/
theorem PreparedChosenModule.source_preExclusion_rank_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (2 ≤ primeRank 3 d.L →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
        ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
          Nat.card d.plusOmega = 2 →
          (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
            (¬ d.localThreeResidual ≤ d.ML) ∧
            d.S ⊓ centralizer (d.localThreeResidual : Set G) =
              d.S ⊓ centralizer (d.L : Set G)) ∧
      ((∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∨
        (¬ d.S ≤ normalizer (d.L : Set G)) ∧ primeRank 3 d.L ≤ 1 ∧
          ∀ P ∈ d.sourceParabolics,
            Nonempty (((P ⊔ d.sylowNormalizer : Subgroup G) ⧸
              pCore 2 (P ⊔ d.sylowNormalizer : Subgroup G)) ≃* Equiv.Perm (Fin 3))) := by
  obtain ⟨d,hZ,hrow,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hrow,s,?_,s.parabolic_placement_or_moved_cubic (h := h) hG hM hJ hu⟩
  intro hr
  refine ⟨s.parabolic_placement_of_threeRank hG hM hJ hu h hr,?_⟩
  intro F hF hout hcard
  exact s.parabolic_family_centralizer_of_threeRank
    (h := h) hG hM hJ hfull hu hr hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01
