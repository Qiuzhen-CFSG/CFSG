module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic
public import CFSG.Quasithin.Chapter15.Section04.SourceReduction
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The actual ordering after the centralizer reduction

The two existing conventions for V(M), the relative normal closure and the
ambient conjugate span, agree. Consequently C_G(Ω₁(Z(T))) = T makes the
source A.5 ordering on maximal two-local overgroups discrete: comparable
members coincide. In the original multiple-overgroup case, every member is
ordering-maximal and there is no unique maximal member.

This proves the literal ordering assertion of 15.4.11(2), without the legacy
Chapter 14 relation certificate. The preceding centralizer theorem is consumed
by InitialSource.Assembly. Source: Aschbacher–Smith, pp.1160–1161.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open ChapterA.Section05To06 FamilySource
variable {G : Type*} [Group G]

/-- The normal closure used by the family construction is the A.5 source module. -/
theorem localV_eq_sourceModule (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    localV T M = sourceModule T M := by
  have hZM : centralOmega T ≤ M := by
    intro z hz
    exact hTM ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).1
  change (normalClosure ((centralOmega T).subgroupOf M : Set M)).map M.subtype =
    conjugateSpanBy (centralOmega T) M
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hZM,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZM)]

/-- Under 15.4.8, an A.5 comparison between two actual maximal locals is equality. -/
theorem eq_of_orderingLE (T : Sylow 2 G)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    {M N : Subgroup G} (hM : M ∈ maximalLocals T) (hN : N ∈ maximalLocals T)
    (hMN : OrderingLE T M N) : M = N := by
  apply hM.1.eq_of_le hN.1.1
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.2] using
      pCoreIn_le_sylow M (T.subtype hM.2)
  have hcentral : M ⊓ centralizer (sourceModule T M : Set G) = M.pCoreIn 2 := by
    rw [← localV_eq_sourceModule T M hM.2]
    exact localV_centralizer T M hM.2 hC
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hMN x hx
  exact N.mul_mem ha.2 (hN.2 (hcoreT (hcentral ▸ hc)))

/-- Every maximal local is maximal for the source ordering. -/
theorem ordering_maximal (T : Sylow 2 G)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    {M : Subgroup G} (hM : M ∈ maximalLocals T) : IsOrderingMaximal T M :=
  ⟨hM, fun _ hN hMN => (eq_of_orderingLE T hC hM hN hMN).symm⟩

/-- The multiple-centralizer-overgroup hypothesis excludes a unique source maximum. -/
theorem not_unique_ordering_maximal [Finite G] (T : Sylow 2 G)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ¬ ∃! M : Subgroup G, IsOrderingMaximal T M := by
  obtain ⟨M, hM, N, hN, hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
  rw [hC] at hM hN
  rintro ⟨P, _, hP⟩
  exact hne ((hP M (ordering_maximal T hC hM)).trans
    (hP N (ordering_maximal T hC hN)).symm)

end CFSG.Quasithin.Chapter15.Section04.InitialSource
