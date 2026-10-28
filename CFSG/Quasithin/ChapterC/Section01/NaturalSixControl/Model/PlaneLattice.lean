module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model

/-!
# Intersections and generation of the three point-core planes

The existing eight-element subgroup table identifies the three mixed planes.
Distinct planes meet in the marked transposition line and generate the full
point core. The proof checks only the table indices, then uses the proved
word coordinates to transfer those facts to the actual S6 subgroups.

These are the finite calculations for MS93 (5.4), printed p.915, in the
binary symplectic source used by Aschbacher--Smith C.1.37.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.Model

private def planeRow (i : Fin 3) : Fin 16 := ![9,10,11] i

private theorem corePlane_table (i : Fin 3) :
    corePlane i = exceptionalSubgroup (planeRow i) := by
  fin_cases i <;> simp [corePlane,planeRow]

private theorem corePlane_word_mem (i : Fin 3) (k : Fin 8) :
    exceptionalWords k ∈ corePlane i ↔ k ∈ exceptionalIndices (planeRow i) := by
  rw [corePlane_table]
  exact exceptionalWord_mem_iff _ _

theorem corePlane_injective : Function.Injective corePlane := by
  intro i j he
  rw [corePlane_table,corePlane_table] at he
  exact (by decide : Function.Injective planeRow) (exceptionalSubgroup_injective he)

theorem corePlane_inf_of_ne {i j : Fin 3} (hne : i ≠ j) :
    corePlane i ⊓ corePlane j = last := by
  ext x
  constructor
  · rintro ⟨hi,hj⟩
    obtain ⟨k,rfl⟩ := (mem_exceptional_iff _).mp (corePlane_le i hi)
    have hi' := (corePlane_word_mem i k).mp hi
    have hj' := (corePlane_word_mem j k).mp hj
    apply exceptionalSubgroup_last ▸ (exceptionalWord_mem_iff 4 k).mpr
    exact (by decide : ∀ i j : Fin 3, i ≠ j → ∀ k : Fin 8,
      k ∈ exceptionalIndices (planeRow i) → k ∈ exceptionalIndices (planeRow j) →
      k ∈ exceptionalIndices 4) i j hne k hi' hj'
  · intro hx
    obtain ⟨k,hk,rfl⟩ := (mem_exceptionalSubgroup_iff 4 _).mp
      (exceptionalSubgroup_last.symm ▸ hx)
    have hi : ∀ i : Fin 3, k ∈ exceptionalIndices (planeRow i) :=
      (by decide : ∀ k : Fin 8, k ∈ exceptionalIndices 4 →
        ∀ i : Fin 3, k ∈ exceptionalIndices (planeRow i)) k hk
    exact ⟨(corePlane_word_mem i k).mpr (hi i),(corePlane_word_mem j k).mpr (hi j)⟩

theorem corePlane_sup_of_ne {i j : Fin 3} (hne : i ≠ j) :
    corePlane i ⊔ corePlane j = E := by
  obtain ⟨r,hr⟩ := (subgroup_le_exceptional_iff (corePlane i ⊔ corePlane j)).mp
    (sup_le (corePlane_le i) (corePlane_le j))
  have hi : exceptionalIndices (planeRow i) ⊆ exceptionalIndices r := by
    intro k hk
    apply (exceptionalWord_mem_iff r k).mp
    rw [←hr]
    exact (le_sup_left : corePlane i ≤ corePlane i ⊔ corePlane j)
      ((corePlane_word_mem i k).mpr hk)
  have hj : exceptionalIndices (planeRow j) ⊆ exceptionalIndices r := by
    intro k hk
    apply (exceptionalWord_mem_iff r k).mp
    rw [←hr]
    exact (le_sup_right : corePlane j ≤ corePlane i ⊔ corePlane j)
      ((corePlane_word_mem j k).mpr hk)
  have he : r = 15 := (by decide : ∀ i j : Fin 3, i ≠ j → ∀ r : Fin 16,
    exceptionalIndices (planeRow i) ⊆ exceptionalIndices r →
    exceptionalIndices (planeRow j) ⊆ exceptionalIndices r → r = 15) i j hne r hi hj
  rw [hr,he,exceptionalSubgroup_exceptional]

end CFSG.Quasithin.ChapterC.NaturalSixControl.Model
