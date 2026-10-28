module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Orbit
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups

/-!
# Reduction of the local-normalizer branch to a nonsolvable orbit quotient

The case W ≤ S is already closed by the weak-closure normalizer comparison.
Otherwise there is an elementary member escaping S and a nontrivial complement
to its component stabilizer. A counterexample to the normalizer containment
also supplies a chief section in J₀S whose residual orbit H has its actual
product kernel H₀ inside the generation target.

If HT/H₀ were solvable, a minimal supplement and the proved solvable
generation theorem would put HT in the target, contradicting the escaping
section. Thus this literal orbit quotient is nonsolvable. To complete E.1.11
one still needs its marked component structure and the rank-one hyperplane
diagonal construction, followed by E.1.10(7) and inheritance. Those conclusions
are not asserted by the present reduction.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.213--214.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Failure of the normalizer branch supplies the source elementary member
and a nontrivial complement acting freely on its component orbit. -/
theorem exists_escaping_complement {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hnot : ¬ localNormalizer T J Ω ≤ generationTarget n T Ω) :
    ∃ A Z : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      ¬ A ≤ stabilizer T J ∧ Z ≤ A ∧ (A ⊓ stabilizer T J) ⊔ Z = A ∧
      Disjoint Z (normalizer (J : Set G)) ∧ Z ≠ ⊥ := by
  obtain ⟨A, hA, hAT, hAS⟩ := exists_member_not_le_stabilizer T J hΩ hnot
  let _ := hΩ.1 A hA
  obtain ⟨Z, hZA, hsup, hdis, hZne⟩ := exists_component_complement T J A hAT hAS
  exact ⟨A, Z, hA, hAT, hAS, hZA, hsup, hdis, hZne⟩

/-- An escaping local normalizer supplies a chief section whose actual
residual-orbit quotient is nonsolvable. The remaining diagonal argument must
rule out this witness; this reduction does not assert E.1.11. -/
theorem exists_escaping_nonsolvable_orbit {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) (J : Subgroup G) {Ω : Set (Subgroup G)}
    (hΩ : IsElementaryFamily Ω) (hJ : IsComponent G J)
    (hnot : ¬ localNormalizer T J Ω ≤ generationTarget n T Ω) :
    ∃ (X : Subgroup (normalizerGroup T J Ω))
      (hchief : ChiefFactor.IsChief X (normalizerKernel n T J Ω))
      (hXN : X ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω)),
      ¬ X.map (normalizerGroup T J Ω).subtype ≤ generationTarget n T Ω ∧
      ¬ IsPGroup 2 (X ⧸ (normalizerKernel n T J Ω).subgroupOf X) ∧
      letI := hchief.normal_upper
      letI := normalizerOrbitKernel_normal n T J X hXN hJ
      ¬ Group.IsSolvable ((normalizerOrbitGroup T J Ω X) ⧸
        (normalizerOrbitKernel n T J Ω X).subgroupOf (normalizerOrbitGroup T J Ω X)) := by
  obtain ⟨X, hchief, hXN, hXM, h2⟩ := exists_escaping_chiefSection T J hΩ hJ.1 hnot
  refine ⟨X, hchief, hXN, hXM, h2, ?_⟩
  let _ := hchief.normal_upper
  let _ := normalizerOrbitKernel_normal n T J X hXN hJ
  intro hsolv
  let _ := hsolv
  apply hXM
  apply escaping_section_le_of_orbit_le T J X hchief h2
  have hOM : normalizerOrbitGroup T J Ω X ≤ generationTarget n T Ω := by
    apply overgroup_le_target_of_solvable_quotient hn T (normalizerOrbitGroup T J Ω X)
      (show (T : Subgroup G) ≤ normalizerOrbitGroup T J Ω X from le_sup_right) hΩ
      ((normalizerOrbitKernel n T J Ω X).subgroupOf (normalizerOrbitGroup T J Ω X))
    exact (subgroupOf_map_subtype _ _).le.trans
      (inf_le_left.trans (normalizerOrbitKernel_le_target n T J hΩ X))
  exact (componentOrbit_le_sup _ _).trans hOM

end CFSG.Quasithin.ChapterE.ChiefOrbit
