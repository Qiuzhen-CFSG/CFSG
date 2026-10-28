module

public import Stellmacher.SectionNine.NineTenNormalizedExtraction

/-!
# The extracted predecessor in the reversed pair of (9.10)

For the actual normalized extraction, conjugating the path vertex at
offset three by its residual conjugator produces a neighbor of the
initial vertex. The penultimate vertex is at distance at most the
critical length from this predecessor. Consequently either its center
lies in the predecessor core or the reversed pair is critical.

Conjugate the offset-two/offset-three path edge and use the extraction's
identity for the normalized initial vertex. Prepend this new edge to
the initial-to-penultimate path segment to obtain the distance bound.
Critical minimality turns a center noncontainment into equality of
distance and hence a critical pair.

This isolates the geometric alternative in Stellmacher (9.10)(5),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. It does not eliminate
the core-containment branch or assume the preceding module noncommutation.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_extracted_predecessor_alternative
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (hb : 2 < cp.length) (second : Γ.Vertex)
    (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData Γ cp.firstStep second (VAt Γ cp.a') E A0 actor)
    (hsecond : IsCriticalPathOffset Γ cp 2 second)
    (hnew : Γ.act data.x⁻¹ second = cp.a) :
    let third := cp.path ⟨3, by omega⟩
    let predecessor := Γ.act data.x⁻¹ third
    let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    Γ.adjacent cp.a predecessor ∧
      Γ.distance penultimate predecessor ≤ cp.length ∧
      (ZAt Γ penultimate ≤ QAt Γ predecessor ∨
        IsCriticalPair Γ penultimate predecessor) := by
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  obtain ⟨index, hindex, hvertex⟩ := hsecond
  have hindexEq : index = ⟨2, by omega⟩ := Fin.ext hindex
  have hsecondEq : cp.path ⟨2, by omega⟩ = second := hindexEq ▸ hvertex
  have hedge : Γ.adjacent second third := by
    have h := cp.path_adj ⟨2, hb⟩
    simpa only [Fin.castSucc_mk, Fin.succ_mk, hsecondEq] using h
  have hpredecessor : Γ.adjacent cp.a predecessor := by
    rw [← hnew]
    exact adjacent_act Γ data.x⁻¹ hedge
  have hbound : Γ.distance penultimate predecessor ≤ cp.length := by
    have hadj : Γ.adjacent predecessor (cp.path ⟨0, by omega⟩) := by
      change Γ.adjacent predecessor (cp.path 0)
      rw [cp.path_start]
      exact Γ.adjacent_symm hpredecessor
    have h := neighbor_path_distance_le Γ cp predecessor 0 (cp.length - 1)
      (Nat.zero_le _) (Nat.sub_le _ _) hadj
    change Γ.distance predecessor penultimate ≤ cp.length - 1 - 0 + 1 at h
    rw [Γ.distance_symm]
    omega
  refine ⟨hpredecessor, hbound, ?_⟩
  by_cases hcontain : ZAt Γ penultimate ≤ QAt Γ predecessor
  · exact Or.inl hcontain
  · right
    have hlower : cp.length ≤ Γ.distance penultimate predecessor := by
      by_contra hlt
      exact hcontain (critical_minimality Γ cp (by omega))
    have hdistance : Γ.distance penultimate predecessor = cp.length := by omega
    refine ⟨?_, hcontain⟩
    rw [hdistance, ← cp.endpoint_distance]
    exact cp.critical.1

end Stellmacher.SectionNine
