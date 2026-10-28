module
public import Theory.GroupTheory.AmalgamGraph.LocalAction

/-!
# Normal Sylows in local permutation kernels

Subgroups of a finite group with normal Sylow p-subgroup inherit that
property. Applied to a graph's full edge stabilizer, this makes the
radius-one kernel p-closed. Its embedded core equals the vertex core
when the edge contains a vertex Sylow, so the vertex core is a Sylow
of the local kernel. The full kernel may still have odd-order elements.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.2)(d), p.119. The proof uses only the stated Sylow properties
of the edge and vertex groups, and permits an infinite completion.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {p : ℕ}

/-- Every p-subgroup of a group with normal Sylow p-subgroup lies in its core. -/
theorem pGroup_le_core_of_core_sylow (B A : Subgroup G) [Finite B]
    (hAB : A ≤ B) (hA : IsPGroup p A)
    (hB : ∃ T : Sylow p B, (T : Subgroup B) = pCore p B) :
    A ≤ B.pCoreIn p := by
  obtain ⟨T, hT⟩ := hB
  let D := A.subgroupOf B
  have hD : IsPGroup p D := hA.comap_subtype
  have hTD : IsPGroup p (D ⊔ pCore p B : Subgroup B) :=
    hD.to_sup_of_normal_right pCore_isPGroup
  have he := T.is_maximal' (hT.symm ▸ hTD) le_sup_right
  have hle : D ≤ pCore p B := by
    rw [← hT]
    exact le_sup_left.trans he.le
  have hm := map_mono (f := B.subtype) hle
  rwa [map_subgroupOf_eq_of_le hAB] at hm

/-- Subgroups of a group with normal Sylow p-subgroup also have normal Sylow. -/
theorem core_sylow_of_le (B D : Subgroup G) [Finite B] (hDB : D ≤ B)
    (hB : ∃ T : Sylow p B, (T : Subgroup B) = pCore p B) :
    ∃ T : Sylow p D, (T : Subgroup D) = pCore p D := by
  let : Finite D := Finite.of_injective (inclusion hDB) (inclusion_injective _)
  obtain ⟨T⟩ := Sylow.nonempty (p := p) (G := D)
  have hTB : (T : Subgroup D).map D.subtype ≤ B.pCoreIn p :=
    pGroup_le_core_of_core_sylow B _ ((map_subtype_le _).trans hDB)
      (T.isPGroup'.map _) hB
  have hTD : (T : Subgroup D).map D.subtype ≤ D.pCoreIn p :=
    (le_inf (map_subtype_le _) hTB).trans (inf_pCoreIn_le_of_le p hDB)
  have hle : (T : Subgroup D) ≤ pCore p D := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hTD (mem_map_of_mem D.subtype hx)
    exact D.subtype_injective he ▸ hy
  exact ⟨T, T.is_maximal' pCore_isPGroup hle |>.symm⟩

/-- Intrinsic normal-Sylow control is invariant under a group isomorphism. -/
theorem core_sylow_equiv [Fact p.Prime] {H D : Type*} [Group H] [Group D] [Finite H]
    (e : H ≃* D) (h : ∃ T : Sylow p H, (T : Subgroup H) = pCore p H) :
    ∃ T : Sylow p D, (T : Subgroup D) = pCore p D := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (T : Subgroup H).map e.toMonoidHom = _
  rw [hT, pCore_map_iso]

/-- A literal embedded Sylow witness transports through an injective map. -/
theorem sylow_witness_map [Fact p.Prime] {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Injective f) (D A : Subgroup G) [Finite D]
    (h : ∃ T : Sylow p D, (T : Subgroup D).map D.subtype = A) :
    ∃ T : Sylow p (D.map f),
      (T : Subgroup (D.map f)).map (D.map f).subtype = A.map f := by
  obtain ⟨T, hT⟩ := h
  let e := D.equivMapOfInjective f hf
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((T : Subgroup D).map e.toMonoidHom).map (D.map f).subtype = _
  rw [← hT, map_map, map_map]
  rfl

/-- Restrict the ambient completion of a marked finite local Sylow. The
proof is at a generic subgroup boundary so concrete completion expressions
need not be unfolded during the dependent Sylow transport. -/
theorem sylow_le_subgroupOf [Fact p.Prime] (D W A : Subgroup G) [Finite D]
    (hDW : D ≤ W)
    (h : ∃ T : Sylow p D, (T : Subgroup D).map D.subtype ≤ A) :
    ∃ T : Sylow p (D.subgroupOf W),
      (T : Subgroup (D.subgroupOf W)).map (D.subgroupOf W).subtype ≤ A.subgroupOf W := by
  obtain ⟨T, hT⟩ := h
  let e := (subgroupOfEquivOfLe hDW).symm
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
  exact hT (mem_map_of_mem D.subtype ht)

open Subgroup.CosetGeometry.RankTwo
variable (F : Bool → Subgroup G)

/-- The full local kernel has its vertex core as a Sylow when the incident
edge has normal Sylow and contains a vertex Sylow. -/
theorem sylow_ballKernel_one [∀ i, Finite (F i)] {v w : Vertex F}
    (hvw : (graph F).Adj v w)
    (hB : ∃ T : Sylow 2 (stabilizer F v ⊓ stabilizer F w : Subgroup G),
      (T : Subgroup (stabilizer F v ⊓ stabilizer F w : Subgroup G)) =
        pCore 2 (stabilizer F v ⊓ stabilizer F w : Subgroup G))
    (T : Sylow 2 (stabilizer F v))
    (hT : (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤
      stabilizer F w) :
    ∃ R : Sylow 2 (ballKernel F v 1),
      (R : Subgroup (ballKernel F v 1)).map (ballKernel F v 1).subtype =
        (stabilizer F v).pCoreIn 2 := by
  let E := stabilizer F v ⊓ stabilizer F w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F v from inf_le_left))
    (inclusion_injective _)
  obtain ⟨R, hR⟩ := core_sylow_of_le E (ballKernel F v 1)
    (ballKernel_one_le_edge F hvw) hB
  refine ⟨R, ?_⟩
  rw [hR]
  exact core_ballKernel_one F hvw T hT
end Theory.GroupTheory.AmalgamGraph
