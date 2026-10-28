module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centers above a self-centralizing subgroup

Suppose `P ≤ T ≤ H`, with `P` specified inside `H`. If `C_H(P) ≤ P`
and `Z(P)` is central in `H`, then the ambient images of `Z(T)` and
`Z(P)` agree. The forward inclusion uses self-centralization; the reverse
uses centrality in the overgroup. No Sylow or finiteness hypothesis is needed.

This supplies the cyclic Sylow-center condition in the involution-centralizer
recognition argument following Aschbacher–Smith, Proposition 6.2.13, p.688.
-/

namespace Subgroup

/-- The center of an intermediate subgroup is the center of the
self-centralizing subgroup, with both sides embedded in the original group. -/
public theorem center_map_eq_of_selfCentralizing
    {G : Type*} [Group G] {H : Subgroup G} (T : Subgroup G) (hTH : T ≤ H)
    (P : Subgroup H) (hPT : P.map H.subtype ≤ T)
    (hC : centralizer (P : Set H) ≤ P)
    (hZ : (center P).map P.subtype ≤ center H) :
    (center T).map T.subtype = ((center P).map P.subtype).map H.subtype := by
  apply le_antisymm
  · rintro x ⟨t, ht, rfl⟩
    let tH : H := ⟨(t : G), hTH t.property⟩
    have hc : tH ∈ centralizer (P : Set H) := by
      intro p hp
      apply Subtype.ext
      exact congrArg (fun a : T => (a : G)) (mem_center_iff.mp ht
        ⟨(p : G), hPT (mem_map_of_mem H.subtype hp)⟩)
    have htP : tH ∈ P := hC hc
    have hz : (⟨tH, htP⟩ : P) ∈ center P := by
      apply mem_center_iff.mpr
      intro p
      exact Subtype.ext (hc p p.property)
    exact mem_map.mpr ⟨tH, mem_map.mpr ⟨⟨tH, htP⟩, hz, rfl⟩, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    have hzP : z ∈ P := map_subtype_le (center P) hz
    have hzT : (z : G) ∈ T := hPT (mem_map_of_mem H.subtype hzP)
    refine mem_map.mpr ⟨⟨(z : G), hzT⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    exact congrArg (fun a : H => (a : G)) (mem_center_iff.mp (hZ hz)
      ⟨(t : G), hTH t.property⟩)

end Subgroup
