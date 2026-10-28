module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer

/-!
# An odd actor from the marked B.4.2(5) constituent

The action field of `MarkedActionEquiv` identifies the whole offender subgroup
with S₅, not just its marked A₅ subgroup. Pull back a transposition and lift it
through the actual constituent realization. This supplies an actor outside the
marked component and retains its action on the literal constituent quotient.

Source: Aschbacher–Smith, B.4.2(5), printed p.86, and the external L₂ case
in the proof of 13.8.20, printed p.954.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {D V E N : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [Group E] [AddCommGroup N] [Module (ZMod 2) N]
  {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
  {σ : Representation (ZMod 2) E N} {J L : Subgroup E}

/-- The marked S₅ subgroup contains a transposition outside the marked A₅. -/
theorem marked_transposition
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ∃ j : J, e.action.groupEquiv j = Equiv.swap 0 1 ∧ (j : E) ∉ L := by
  let j := e.action.groupEquiv.symm (Equiv.swap 0 1)
  have hj : e.action.groupEquiv j = Equiv.swap 0 1 := e.action.groupEquiv.apply_symm_apply _
  refine ⟨j, hj, ?_⟩
  intro hL
  have hc := e.compatible ⟨j, hL⟩
  have hje : (⟨(⟨j, hL⟩ : L), e.contained hL⟩ : J) = j := rfl
  rw [hje, hj] at hc
  have hmem := (e.subgroupEquiv ⟨j, hL⟩).property
  rw [← hc] at hmem
  have hn : Equiv.swap (0 : Fin 5) 1 ∉ alternatingGroup (Fin 5) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact hn hmem

/-- A genuine ambient actor realizes this odd action on the constituent.
In particular, it lies outside K; no ambient product isomorphism is assumed. -/
theorem ConstituentRealization.exists_odd_actor
    (r : ConstituentRealization ρ K σ L)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ∃ g : r.actor, ∃ j : J,
      r.groupMap g = (j : E) ∧ e.action.groupEquiv j = Equiv.swap 0 1 ∧
      r.groupMap g ∉ L ∧ (g : D) ∉ K ∧
      ∀ v : N, e.action.linearEquiv (σ (r.groupMap g) v) =
        BinaryPermutation.naturalRepresentation (Fin 5) (Equiv.swap 0 1)
          (e.action.linearEquiv v) := by
  obtain ⟨j, hj, hL⟩ := marked_transposition e
  obtain ⟨g, hg⟩ := r.surjective (j : E)
  refine ⟨g, j, hg, hj, hg ▸ hL, ?_, ?_⟩
  · intro hk
    have h := r.component_map ⟨g, hk⟩
    change r.groupMap g = (r.component ⟨g, hk⟩ : E) at h
    exact hL (hg ▸ h.symm ▸ (r.component ⟨g, hk⟩).property)
  · intro v
    rw [hg]
    exact (e.action.intertwines j v).trans (by rw [hj])

/-- An odd marked permutation cannot induce an inner automorphism of the
marked A₅. This uses the faithful conjugation action S₅ → Aut(A₅). -/
theorem marked_odd_not_inner
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)))
    (j : J) (hj : e.action.groupEquiv j ∉ alternatingGroup (Fin 5)) :
    ¬ ∃ l : L, ∀ x : L,
      (j : E) * x * (j : E)⁻¹ = (l : E) * x * (l : E)⁻¹ := by
  rintro ⟨l, hl⟩
  have he : (MulAut.conjNormal (e.action.groupEquiv j) :
      MulAut (alternatingGroup (Fin 5))) =
      MulAut.conjNormal (e.subgroupEquiv l).val := by
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := e.subgroupEquiv.surjective a
    apply Subtype.ext
    have hx : j * (⟨x, e.contained x.property⟩ : J) * j⁻¹ =
        (⟨l, e.contained l.property⟩ : J) * ⟨x, e.contained x.property⟩ *
          (⟨l, e.contained l.property⟩ : J)⁻¹ := Subtype.ext (hl x)
    have hh := congrArg e.action.groupEquiv hx
    simpa only [map_mul, map_inv, e.compatible, MulAut.conjNormal_apply] using hh
  have hsame := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).injective he
  exact hj (hsame ▸ (e.subgroupEquiv l).property)

/-- The realized S₅ constituent supplies an ambient actor whose action on K
is outer. This form avoids requiring the constituent and tensor markings of
A₅ to be identical. -/
theorem ConstituentRealization.exists_outer_actor
    (r : ConstituentRealization ρ K σ L)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ∃ g : r.actor, ¬ ∃ k : K, ∀ x : K,
      (g : D) * x * (g : D)⁻¹ = (k : D) * x * (k : D)⁻¹ := by
  obtain ⟨g, j, hg, hj, _, _, _⟩ := r.exists_odd_actor e
  refine ⟨g, ?_⟩
  rintro ⟨k, hk⟩
  have hodd : e.action.groupEquiv j ∉ alternatingGroup (Fin 5) := by
    rw [hj]
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  apply marked_odd_not_inner e j hodd
  refine ⟨r.component k, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := r.component.surjective x
  have he : g * (⟨y, r.contains y.property⟩ : r.actor) * g⁻¹ =
      (⟨k, r.contains k.property⟩ : r.actor) * ⟨y, r.contains y.property⟩ *
        (⟨k, r.contains k.property⟩ : r.actor)⁻¹ := Subtype.ext (hk y)
  have hh := congrArg r.groupMap he
  simpa only [map_mul, map_inv, r.component_map, hg] using hh

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
end
