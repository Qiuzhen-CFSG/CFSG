module

public import Theory.GroupTheory.SaturatedCentralizerTransport

/-!
# Conjugating a commuting actor together with an element centralizer

A p-subgroup centralizing an element of a Sylow subgroup can be moved into
that Sylow while making the element's Sylow centralizer an actual Sylow of
its ambient centralizer. First saturate the element centralizer, then adjust
the conjugator inside that centralizer to carry the entire actor into it.

This is ordinary Sylow conjugacy, used for the local subgroups in
Aschbacher--Smith E.1.2, printed p.210. No conclusion about the structure of
the selected centralizer is asserted.
-/

public section
open Subgroup

namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Keep the whole commuting actor when arranging a Sylow centralizer. -/
theorem exists_conj_actor_with_sylow_centralizer (T : Sylow p G)
    (A : Subgroup G) (hA : IsPGroup p A) (z : G) (hzT : z ∈ T)
    (hAC : A ≤ centralizer ({z} : Set G)) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ∃ S : Sylow p (centralizer ({(MulAut.conj g) z} : Set G)),
        (S : Subgroup (centralizer ({(MulAut.conj g) z} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({(MulAut.conj g) z} : Set G)) := by
  obtain ⟨t, hzt, hmax⟩ := T.exists_conjugate_with_saturated_centralizer ⟨z, hzT⟩
  let E := (centralizer ({t} : Set T)).map (T : Subgroup G).subtype
  have hE : E = (T : Subgroup G) ⊓ centralizer ({(t : G)} : Set G) :=
    map_subtype_centralizer_singleton _ _
  have hEp : IsPGroup p E := (T.isPGroup'.to_subgroup _).map _
  have hEC : E ≤ centralizer ({(t : G)} : Set G) := hE ▸ inf_le_right
  obtain ⟨g, hg, hAg⟩ := exists_conj_into_saturated_centralizer
    (t : G) z E A hEp hA hEC hAC hmax hzt
  refine ⟨g, hAg.trans (hE ▸ inf_le_left), ?_⟩
  rw [hg]
  let C := centralizer ({(t : G)} : Set G)
  refine ⟨{ toSubgroup := (T : Subgroup G).subgroupOf C
            isPGroup' := T.isPGroup'.comap_subtype
            is_maximal' := ?_ }, rfl⟩
  intro Q hQ hTQ
  have he : Q.map C.subtype = E := hmax _ (hQ.map _) (by
    intro x hx
    change x ∈ E at hx
    have hx' := hE ▸ hx
    exact ⟨⟨x, hx'.2⟩, hTQ hx'.1, rfl⟩) (map_subtype_le _)
  apply le_antisymm _ hTQ
  intro x hx
  have hm := mem_map_of_mem C.subtype hx
  rw [he, hE] at hm
  exact hm.1

end Sylow
