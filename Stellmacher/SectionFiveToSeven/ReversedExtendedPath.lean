module

public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Reverse the internal segment and retain both new endpoint offsets

For a critical path of length greater than three, adjoin a supplied neighbor
of its initial vertex and a supplied neighbor of its preterminal vertex to
the reversed internal segment. The resulting path retains its exact new
endpoints, the preterminal vertex at offset one, and the original first step
at offset b-2. Every consecutive pair remains adjacent.

The construction uses the original path in reverse between the two new
endpoints. The first and last edges are the supplied neighbor incidences;
the middle edges are reversed original path edges. It makes no new choice
of a shortest path and does not assert criticality of the new pair.

This shared graph construction occurs in Stellmacher (9.9)(3), printed p.56,
and the reversed critical-pair argument of (9.10)(5), printed pp.57-58.
It was extracted from the original private (9.9) proof without changing the
retained offsets or introducing any Section Nine context dependency.
-/

namespace Stellmacher.SectionsFiveToSeven.SevenSix
open CosetGraphContext
universe u

public theorem reversed_extended_path
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ) (hb : 3 < cp.length)
    (previous neighbor : Γ.Vertex)
    (hprevious : previous ∈ neighborhood Γ cp.a)
    (hneighbor : neighbor ∈ neighborhood Γ (cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    ∃ path : Fin (cp.length+1) → Γ.Vertex,
      path 0 = neighbor ∧ path ⟨cp.length,Nat.lt_succ_self _⟩ = previous ∧
      path ⟨1,by omega⟩ = cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∧
      path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = cp.firstStep ∧
      ∀ index : Fin cp.length, Γ.adjacent (path index.castSucc) (path index.succ) := by
  let path : Fin (cp.length+1) → Γ.Vertex := fun i =>
    if i.val=0 then neighbor else if i.val=cp.length then previous
    else cp.path ⟨cp.length-1-i.val,by omega⟩
  have hstart : path 0 = neighbor := by simp [path]
  have hend : path ⟨cp.length,Nat.lt_succ_self _⟩ = previous := by
    simp [path,show cp.length≠0 by omega]
  have hfirst : path ⟨1,by omega⟩ = cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
    simp only [path,Nat.one_ne_zero,↓reduceIte,show 1≠cp.length by omega]
    apply congrArg cp.path
    apply Fin.ext
    simp only []
    omega
  have hback : path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = cp.firstStep := by
    simp only [path,show cp.length-2≠0 by omega,↓reduceIte,show cp.length-2≠cp.length by omega]
    rw [← cp.path_first]
    apply congrArg cp.path
    apply Fin.ext
    simp only []
    omega
  have hlastInner : path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = cp.a := by
    simp only [path,show cp.length-1≠0 by omega,↓reduceIte,show cp.length-1≠cp.length by omega]
    rw [← cp.path_start]
    apply congrArg cp.path
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  refine ⟨path,hstart,hend,hfirst,hback,?_⟩
  intro i
  by_cases hzero : i.val=0
  · have hleft : i.castSucc = (0 : Fin (cp.length+1)) := Fin.ext hzero
    have hright : i.succ = (⟨1,by omega⟩ : Fin (cp.length+1)) := Fin.ext (by simp; omega)
    rw [hleft,hright,hstart,hfirst]
    exact Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  by_cases hlast : i.val+1=cp.length
  · have hleft : i.castSucc = (⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (cp.length+1)) :=
      Fin.ext (by simp; omega)
    have hright : i.succ = (⟨cp.length,Nat.lt_succ_self _⟩ : Fin (cp.length+1)) := Fin.ext hlast
    rw [hleft,hright,hlastInner,hend]
    exact (mem_neighborhood_iff_adjacent Γ).mp hprevious
  have hile : i.val < cp.length := i.isLt
  have hleftNot : i.val≠cp.length := by omega
  have hrightZero : i.val+1≠0 := by omega
  simp only [path,Fin.val_castSucc,Fin.val_succ,hzero,hleftNot,hrightZero,hlast,↓reduceIte]
  have hedge := cp.path_adj ⟨cp.length-2-i.val,by omega⟩
  apply Γ.adjacent_symm
  convert hedge using 1 <;> apply congrArg cp.path <;> apply Fin.ext <;> simp <;> omega


end Stellmacher.SectionsFiveToSeven.SevenSix
