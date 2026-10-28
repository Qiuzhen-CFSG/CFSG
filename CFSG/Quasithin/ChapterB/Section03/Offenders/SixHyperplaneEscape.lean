module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six

/-!
# Half-order subgroups escaping the six-letter plane radical

The sixteen-subgroup lattice of three disjoint transpositions supplies a
subgroup of index at most two in every subgroup of order at least four.
An explicit even conjugator carries it into the canonical Sylow subgroup
but outside the plane radical. Only the eight-word cube is evaluated.
For subgroups already outside the radical the identity conjugator suffices.
SixThompsonImage applies this calculation to actual maximum elementary images.
Source: Aschbacher–Smith B.3.4(2)(vi), pp.84–85, used in 13.2.2(10), p.878.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB.Offenders.Six

private def selected (r : Fin 16) : Fin 16 :=
  ![0,0,0,0,0,0,0,0,3,5,6,6,5,3,3,13] r

private def conjugator (r : Fin 16) : Perm :=
  let g := Equiv.swap 1 2 * Equiv.swap 4 5
  let a := Equiv.swap 2 4 * Equiv.swap 3 5
  let b := Equiv.swap 0 4 * Equiv.swap 1 5
  ![1,1,1,1,1,1,1,1,g,g*a,g*b,g*b,g*a,g,g,g] r

private theorem certificate (r : Fin 16) (hr : 8 ≤ r.val) :
    dLatticeIndices (selected r) ⊆ dLatticeIndices r ∧
    (dLatticeIndices r).card ≤ 2 * (dLatticeIndices (selected r)).card ∧
    conjugator r ∈ alternatingGroup (Fin 6) ∧
    (∀ i ∈ dLatticeIndices (selected r), ∃ j,
      sylowWords j = (MulAut.conj (conjugator r)) (dWords i)) ∧
    (∃ i ∈ dLatticeIndices (selected r), ∀ j,
      dWords j ≠ (MulAut.conj (conjugator r)) (dWords i)) := by
  have h : ∀ r : Fin 16, 8 ≤ r.val →
    dLatticeIndices (selected r) ⊆ dLatticeIndices r ∧
    (dLatticeIndices r).card ≤ 2 * (dLatticeIndices (selected r)).card ∧
    conjugator r ∈ alternatingGroup (Fin 6) ∧
    (∀ i ∈ dLatticeIndices (selected r), ∃ j,
      sylowWords j = (MulAut.conj (conjugator r)) (dWords i)) ∧
    (∃ i ∈ dLatticeIndices (selected r), ∀ j,
      dWords j ≠ (MulAut.conj (conjugator r)) (dWords i)) := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide
  exact h r hr

theorem exists_half_conjugate_escape (A : Subgroup Perm)
    (hA : A ≤ sylowCarrier) (hc : 2 < Nat.card A) :
    ∃ C : Subgroup Perm, C ≤ A ∧ Nat.card A ≤ 2 * Nat.card C ∧
      ∃ g : alternatingGroup (Fin 6),
        C.map (MulAut.conj g.val).toMonoidHom ≤ sylowCarrier ∧
        ¬ C.map (MulAut.conj g.val).toMonoidHom ≤ D 6 := by
  classical
  by_cases hd : A ≤ D 6
  · obtain ⟨r,rfl⟩ := (subgroup_le_D_iff A).mp hd
    have hr : 8 ≤ r.val := by
      rw [card_dLattice] at hc
      have hh : ∀ r : Fin 16, 2 < (dLatticeIndices r).card → 8 ≤ r.val := by decide
      exact hh r hc
    obtain ⟨hle,hcard,hg,hS,hout⟩ := certificate r hr
    refine ⟨dLattice (selected r),(dLattice_le_iff _ _).mpr hle,?_,
      ⟨conjugator r,hg⟩,?_,?_⟩
    · simpa only [card_dLattice] using hcard
    · rintro _ ⟨x,⟨i,hi,rfl⟩,rfl⟩
      exact (mem_sylowCarrier_iff _).mpr (hS i hi)
    · intro hb
      obtain ⟨i,hi,hn⟩ := hout
      have hh := hb (mem_map_of_mem (MulAut.conj (conjugator r)).toMonoidHom
        ((dWords_mem_dLattice _ _).mpr hi))
      obtain ⟨j,hj⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hh
      exact hn j hj
  · refine ⟨A,le_rfl,by omega,1,?_,?_⟩
    · change A.map (MonoidHom.id _) ≤ _
      simpa only [map_id] using hA
    · change ¬ A.map (MonoidHom.id _) ≤ _
      simpa only [map_id] using hd

end CFSG.Quasithin.ChapterB.Offenders.Six
