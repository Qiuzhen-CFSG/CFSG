module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Relative rank-one Sylow overgroups

An actor normalizing a local group with the rank-one Sylow overgroup property
either contains that group or normalizes the marked Sylow. In the proper
intersection case every actor conjugate of the Sylow lies in its local
normalizer and therefore in the same Sylow. Only relative normality is used;
the ambient completion can be infinite.

This is the relative-normality version of
`Subgroup.RankOneSylowExtension.le_or_le_normalizer`, used for the actual
enlarged local groups in DGS (6.2)(a).

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.2)(a), printed p.119.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- A subgroup normalizing a rank-one local group either contains it or
normalizes its marked Sylow. Normality is only relative to the actor. -/
theorem relative_rankOne_overgroup {p : ℕ} (L M : Subgroup G)
    (hn : M ≤ normalizer (L : Set G)) (T : Sylow p L)
    (hproper : ∀ H : Subgroup L, (T : Subgroup L) ≤ H → H ≠ ⊤ →
      H ≤ normalizer (T : Set L))
    (hTM : (T : Subgroup L).map L.subtype ≤ M) :
    L ≤ M ∨ M ≤ normalizer ((T : Subgroup L).map L.subtype : Set G) := by
  by_cases hLM : L ≤ M
  · exact Or.inl hLM
  right
  have hTH : (T : Subgroup L) ≤ M.subgroupOf L := map_le_iff_le_comap.mp hTM
  have hH : M.subgroupOf L ≠ ⊤ := fun he => hLM (subgroupOf_eq_top.mp he)
  have hHN := hproper _ hTH hH
  apply le_normalizer_iff.mpr
  intro m hm x hx
  obtain ⟨u, hu, rfl⟩ := hx
  let e : MulAut L := L.normalizerMonoidHom ⟨m, hn hm⟩
  have heH : (T : Subgroup L).map e.toMonoidHom ≤ M.subgroupOf L := by
    rintro _ ⟨v, hv, rfl⟩
    change m * (v : G) * m⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hm (hTM (mem_map_of_mem _ hv))) (M.inv_mem hm)
  have heT : (T : Subgroup L).map e.toMonoidHom ≤ (T : Subgroup L) := by
    have hi := (T.isPGroup'.map e.toMonoidHom).inf_normalizer_sylow T
    rw [inf_eq_left.mpr (heH.trans hHN)] at hi
    exact inf_eq_left.mp hi.symm
  exact mem_map.mpr ⟨e u, heT (mem_map_of_mem _ hu), rfl⟩
end Theory.GroupTheory.AmalgamGraph
