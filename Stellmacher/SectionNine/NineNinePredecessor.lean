module

public import Stellmacher.SectionNine.NineNineInitialInputs

/-!
# A distinct predecessor for Stellmacher (9.9)

The initial stabilizer cannot be contained in the first-step stabilizer:
generation would make the latter the whole group, contradicting its nontrivial
two-core and the ambient local group's trivial two-core. An initial stabilizer
element outside the first-step stabilizer moves that neighbor to a distinct
neighbor. This proves the predecessor choice used before (9.9)(2) on printed
p.56 / PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_nine_exists_previous
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ∃ previous : ctx.Γ.Vertex,
      previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        previous ≠ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hgenerate : GAt Γ cp.a ⊔ GAt Γ cp.firstStep = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · change stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤
      rw [hedge.1, hedge.2]
      exact ctx.sectionSeven.generated
    · change stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤
      rw [hedge.1, hedge.2, sup_comm]
      exact ctx.sectionSeven.generated
  have hnot : ¬ GAt Γ cp.a ≤ GAt Γ cp.firstStep := by
    intro hle
    have htop : GAt Γ cp.firstStep = ⊤ := by
      rwa [sup_eq_right.mpr hle] at hgenerate
    have hcoreNe := (edge_local_data ctx.sectionSeven Γ cp).2.1.1.2.2.1
    change twoCoreIn (GAt Γ cp.firstStep) ≠ ⊥ at hcoreNe
    apply hcoreNe
    rw [htop, twoCoreIn]
    have hsubtype : (⊤ : Subgroup G).subtype =
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom := rfl
    rw [hsubtype, pCore_map_iso, ctx.sectionSeven.twoCore_eq_bot]
  obtain ⟨actor, hactor, hmove⟩ := Set.not_subset.mp hnot
  have hfix : Γ.act actor cp.a = cp.a :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.a) actor).mp hactor
  refine ⟨Γ.act actor cp.firstStep, ?_, ?_⟩
  · apply (mem_neighborhood_iff_adjacent Γ).mpr
    rw [← hfix]
    exact adjacent_act Γ actor cp.firstStep_adj
  · intro heq
    exact hmove ((Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) actor).mpr heq)

end Stellmacher.SectionNine
