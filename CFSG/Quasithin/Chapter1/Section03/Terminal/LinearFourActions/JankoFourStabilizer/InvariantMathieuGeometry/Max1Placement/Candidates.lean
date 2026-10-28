module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction

/-!
# Local max1 overgroups and their transport

Separate the existence of a Mathieu overgroup from its invariance under an
automorphism. Candidates retain an actual isomorphism with the certified max1
subgroup and a Sylow-local C-component witness. Containment of the original
ambient Sylow suffices for that local witness: restrict the C-component of
the join and use the Sylow subgroup inside the overgroup. Ambient isomorphisms
preserve every candidate field.

The two concrete contracts at the end remain unproved geometric obligations.
The fixed-point contract accepts candidate existence as an explicit premise,
so its proof can be developed independently of the existence calculation.

Source: Aschbacher–Smith, A.3.10–12, especially A.3.12(17) and its proof by
Sylow overgroups, printed pp.46–48; proof of 1.3.9, p.514. GLS3 Table 5.3i
describes the relevant J₄ local groups. The literal matrix max1 certificates
are in `Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
open Section02.LocalModels
universe u v
variable {G : Type u} [Group G] {G' : Type v} [Group G']

namespace Max1Placement

/-- The local condition restricts when both subgroups lie in the new ambient group. -/
theorem localCComponents_subgroupOf {A S H : Subgroup G}
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hAH : A ≤ H) (hSH : S ≤ H) :
    A.subgroupOf H ∈ ChapterA.Section03.localCComponents (S.subgroupOf H) := by
  let e := (Subgroup.subgroupOfEquivOfLe (sup_le hAH hSH)).symm
  have h := hlocal.map_equiv e
  have he : (A.subgroupOf (A ⊔ S)).map e.toMonoidHom =
      (A.subgroupOf H).subgroupOf ((A ⊔ S).subgroupOf H) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, x.property⟩, hx, rfl⟩
  rw [he, Subgroup.subgroupOf_sup hAH hSH] at h
  exact h

private theorem map_subgroupOf_equiv (A H : Subgroup G) (e : G ≃* G') :
    (A.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hax⟩
    have haH : a ∈ H := by
      obtain ⟨b, hb, heb⟩ := x.property
      have hab : a = b := e.injective (hax.trans heb.symm)
      exact hab.symm ▸ hb
    exact ⟨⟨a, haH⟩, ha, Subtype.ext hax⟩

private theorem local_map_equiv [Finite G] {A S : Subgroup G}
    (hA : A ∈ ChapterA.Section03.localCComponents S) (e : G ≃* G') :
    A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact Section02.localCComponents_map_of_solvable_ker hA e.toMonoidHom

/-- Subgroups admitting the required max1 comparison and local embedding.
This family imposes no invariance condition and carries no chosen isomorphism. -/
@[expose] def candidates (A : Subgroup G) : Set (Subgroup G) :=
  {H | A ≤ H ∧ Nonempty (H ≃* certifiedMathieuSubgroup) ∧
    ∃ T : Sylow 2 H, A.subgroupOf H ∈ ChapterA.Section03.localCComponents T}

/-- A max1 overgroup containing the original Sylow is a candidate.
In particular, the last field is a deduction from containment, not extra geometry. -/
theorem mem_candidates_of_sylow_le {A H : Subgroup G} (S : Sylow 2 G)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hAH : A ≤ H) (hSH : (S : Subgroup G) ≤ H)
    (e : H ≃* certifiedMathieuSubgroup) : H ∈ candidates A :=
  ⟨hAH, ⟨e⟩, S.subtype hSH, localCComponents_subgroupOf hlocal hAH hSH⟩

/-- Ambient isomorphisms carry the entire candidate family to the corresponding family. -/
theorem map_mem_candidates [Finite G] {A H : Subgroup G}
    (hH : H ∈ candidates A) (e : G ≃* G') :
    H.map e.toMonoidHom ∈ candidates (A.map e.toMonoidHom) := by
  obtain ⟨hAH, ⟨f⟩, T, hT⟩ := hH
  let g := e.subgroupMap H
  refine ⟨Subgroup.map_mono hAH, ⟨g.symm.trans f⟩,
    T.mapSurjective (f := g.toMonoidHom) g.surjective, ?_⟩
  have h := local_map_equiv hT g
  rw [map_subgroupOf_equiv] at h
  exact h

/-- Stabilizing A preserves the candidate family, including its Sylow-local field. -/
theorem map_mem_candidates_of_invariant [Finite G] {A H : Subgroup G}
    (hH : H ∈ candidates A) (α : MulAut G) (hA : A.map α.toMonoidHom = A) :
    H.map α.toMonoidHom ∈ candidates A := by
  simpa only [hA] using map_mem_candidates hH α

/-- A fixed candidate supplies every field of the required placement. -/
noncomputable def placementOfFixedCandidate {A H : Subgroup G} {α : MulAut G}
    (hH : H ∈ candidates A) (hfix : H.map α.toMonoidHom = H) :
    LocalMax1Placement A α where
  overgroup := H
  le_overgroup := hH.1
  invariant := hfix
  modelEquiv := Classical.choice hH.2.1
  sylow := Classical.choose hH.2.2
  source_local := Classical.choose_spec hH.2.2

/-- Forgetting a placement's invariance gives a candidate in the same literal subgroup. -/
theorem placement_mem_candidates {A : Subgroup G} {α : MulAut G}
    (D : LocalMax1Placement A α) : D.overgroup ∈ candidates A :=
  ⟨D.le_overgroup, ⟨D.modelEquiv⟩, D.sylow, D.source_local⟩

/-- The remaining existence obligation, separated from any automorphism action. -/
@[expose] def ConcreteCandidateExistenceTheorem : Prop :=
  ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
    A ∈ ChapterA.Section03.localCComponents S → (candidates A).Nonempty

/-- The remaining fixed-point obligation, with existence supplied independently.
An odd-cardinality or uniqueness argument may prove this, but neither is assumed here. -/
@[expose] def ConcreteCandidateFixedPointTheorem : Prop :=
  ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
    A ∈ ChapterA.Section03.localCComponents S → (candidates A).Nonempty →
    ∀ α : MulAut Janko4.Model, (∃ n : ℕ, α ^ (2 ^ n) = 1) →
      A.map α.toMonoidHom = A → ∃ H ∈ candidates A, H.map α.toMonoidHom = H

end Max1Placement
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
