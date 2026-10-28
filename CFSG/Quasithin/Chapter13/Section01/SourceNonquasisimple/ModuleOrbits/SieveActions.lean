module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.SylowIrreducible

/-!
# Local quaternion actions in the centralizer sieve

The inclusion C_T(u)∩L ≤ C_T(u) preserves the original odd Frattini
action. A faithful quaternion subgroup in the smaller image therefore
embeds in the full Sylow-centralizer image. Its irreducibility supplies
both clauses of the downstream sieve outside the symmetric-three row.

Source: Aschbacher--Smith, proof of 13.1.12, printed pp.873--874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Enlarge the acting subgroup while retaining both quotient maps. -/
theorem sylow_quaternion_of_component_quaternion (h : Context T L p) (u : G)
    (hq : ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G)) (XiP p L)
      (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
      Function.Injective f) :
    ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) (XiP p L)
      (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))).range,
      Function.Injective f := by
  let A := ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G)
  let B := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  have hAB : A ≤ B := inf_le_inf_right _ inf_le_left
  let ρ := xiFrattiniAction A (XiP p L)
    (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))
  let τ := xiFrattiniAction B (XiP p L)
    (XiP_invariant p (inf_le_left.trans h.sylow_normalizes))
  have hle : ρ.range ≤ τ.range := by
    rintro _ ⟨a,rfl⟩
    refine ⟨inclusion hAB a,?_⟩
    exact (xiFrattiniAction_restrict hAB
      (XiP_invariant p (inf_le_left.trans h.sylow_normalizes)) a).symm
  obtain ⟨f,hf⟩ := hq
  exact ⟨(inclusion hle).comp f, (inclusion_injective hle).comp hf⟩

/-- The quaternion rows construct the exact `SieveActions` consumed by
the source centralizer sieve. Model construction remains with the caller. -/
theorem sieveActions_of_component_quaternions (h : Context T L p)
    (hq : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f) : SieveActions h where
  quaternion u s hnt _ := sylow_quaternion_of_component_quaternion h u (hq u s hnt)
  symmetric_three u s hnt hred := (hred (h.sylow_radical_irreducible_of_quaternion
    (sylow_quaternion_of_component_quaternion h u (hq u s hnt)))).elim

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
