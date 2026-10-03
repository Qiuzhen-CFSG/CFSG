module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# Containment and invariance of the exact distance-one conjugate closure

The Vstar in Stellmacher (9.1) is the terminal-stabilizer conjugate closure of
the initial center intersected with the terminal core. Normality of that core
bounds every generator and hence the entire closure. The terminal stabilizer
normalizes the closure by multiplying conjugators.

At critical distance one the terminal core lies in the distinguished edge
Sylow subgroup. Thus Vstar also lies in that Sylow and in both endpoint
stabilizers. These facts use only the genuine local context and path length;
neither local classification nor an order-eight witness is assumed. They form
a common prerequisite for residual-action and local-normalizer constructions.
Source: Stellmacher (9.1), Journal of Algebra 190 (1997), p.48.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

private theorem endpoint_eq_firstStep
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1) :
    ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
  rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
  congr 1
  exact Fin.ext hlength

public theorem distance_one_vstar_containments
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    NormalIn Vstar (GAt ctx.Γ ctx.criticalPath.a') ∧
      Vstar ≤ QAt ctx.Γ ctx.criticalPath.a' ∧ Vstar ≤ T ∧
      Vstar ≤ GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.a' := by
  let seed := ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a'
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let Vstar := conjugateClosure seed terminal
  have hcore : Vstar ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    apply (Subgroup.closure_le _).mpr
    rintro actor ⟨conjugator, element, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (SevenSix.stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a'
        conjugator.property) (element : G)).mp element.property.2
  have hterminal : Vstar ≤ terminal := hcore.trans (by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ terminal
    rw [ctx.Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le terminal)
  have hnormalizes : terminal ≤ Subgroup.normalizer (Vstar : Set G) := by
    rw [show Vstar = conjugateClosure seed terminal from rfl,
      conjugateClosure, Subgroup.le_normalizer_closure_iff]
    intro actor hactor element helement
    obtain ⟨conjugator, generator, rfl⟩ := helement
    apply Subgroup.subset_closure
    refine ⟨⟨actor * conjugator, terminal.mul_mem hactor conjugator.property⟩,
      generator, ?_⟩
    change actor * ((conjugator : G) * (generator : G) * (conjugator : G)⁻¹) *
      actor⁻¹ = (actor * (conjugator : G)) * (generator : G) *
        (actor * (conjugator : G))⁻¹
    group
  have hVstarT : Vstar ≤ T := hcore.trans (by
    rw [endpoint_eq_firstStep ctx hlength]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ
      ctx.criticalPath).2)
  refine ⟨⟨hterminal,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hterminal).mpr hnormalizes⟩,
    hcore, hVstarT, ?_⟩
  apply hVstarT.trans
  rw [endpoint_eq_firstStep ctx hlength]
  exact ctx.criticalPath.S_le_edge_stabilizers

end Stellmacher.SectionNine
