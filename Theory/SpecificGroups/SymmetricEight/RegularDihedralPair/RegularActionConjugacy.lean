module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Model
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Marking a regular dihedral action

A fixed-point-free action of `D₈` on eight points is regular.  The orbit
bijection at a chosen point therefore conjugates it to the fixed concrete
regular dihedral subgroup used by the Held recognition source.
-/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

private abbrev D8 := DihedralGroup 4
private abbrev P8' := Equiv.Perm (Fin 8)

private def standardD8 : D8 →* P8' where
  toFun
    | .r i => r ^ (i.val % 4)
    | .sr i => r ^ ((4 - i.val) % 4) * s
  map_one' := by decide +revert +kernel
  map_mul' := by
    intro x y
    rcases x with (i | i) <;> rcases y with (j | j) <;> decide +revert +kernel

private theorem standardD8_r_mem (i : ZMod 4) : standardD8 (.r i) ∈ twoGroup := by
   decide +revert +kernel
private theorem standardD8_sr_mem (i : ZMod 4) : standardD8 (.sr i) ∈ twoGroup := by
   decide +revert +kernel
private theorem standardD8_range : standardD8.range = twoGroup := by
   apply le_antisymm
   · rintro _ ⟨x, rfl⟩
     rcases x with i | i
     · exact standardD8_r_mem i
     · exact standardD8_sr_mem i
   · intro g hg
     obtain ⟨i, rfl⟩ := hg
     fin_cases i
     · exact ⟨.r 0, by decide⟩
     · exact ⟨.r 1, by decide⟩
     · exact ⟨.r 2, by decide⟩
     · exact ⟨.r 3, by decide⟩
     · exact ⟨.sr 0, by decide⟩
     · exact ⟨.sr 3, by decide⟩
     · exact ⟨.sr 2, by decide⟩
     · exact ⟨.sr 1, by decide⟩

theorem regular_dihedral_conjugacy
    (d : DihedralGroup 4 →* Equiv.Perm (Fin 8)) (_hd : Function.Injective d)
    (hfree : ∀ x : DihedralGroup 4, x ≠ 1 → ∀ i, d x i ≠ i) :
    ∃ c : Equiv.Perm (Fin 8),
      d.range.map (MulAut.conj c).toMonoidHom = twoGroup := by
  have horbit_inj : Function.Injective (fun x : D8 => d x 0) := by
    intro x y hxy
    by_contra hxy'
    have hxy'0 : d x 0 = d y 0 := hxy
    have hz : d (y⁻¹ * x) 0 = 0 := by
      calc
        d (y⁻¹ * x) 0 = d y⁻¹ (d x 0) := by rw [map_mul]; rfl
        _ = d y⁻¹ (d y 0) := by rw [hxy'0]
        _ = 0 := by simp
    exact (hfree (y⁻¹ * x) (by
      intro he
      apply hxy'
      exact (inv_mul_eq_one.mp he).symm) 0 hz).elim
  have horbit : Function.Bijective (fun x : D8 => d x 0) := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨horbit_inj, ?_⟩
    simp [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hstd : Function.Bijective (fun x : D8 => standardD8 x 0) := by
    decide +revert +kernel
  let ed : D8 ≃ Fin 8 := Equiv.ofBijective (fun x : D8 => d x 0) horbit
  let ee : D8 ≃ Fin 8 := Equiv.ofBijective (fun x : D8 => standardD8 x 0) hstd
  let c : P8' := ed.symm.trans ee
  have hc (x : D8) : c (d x 0) = standardD8 x 0 := by
    change (ed.symm.trans ee) (ed x) = ee x
    simp
  have hconj (x : D8) : MulAut.conj c (d x) = standardD8 x := by
    apply Equiv.ext
    intro y
    obtain ⟨z, hz⟩ := ee.surjective y
    rw [MulAut.conj_apply]
    simp only [Equiv.Perm.mul_apply]
    rw [← hz]
    change c (d x (c⁻¹ (ee z))) = standardD8 x (ee z)
    have hce : c (d z 0) = ee z := hc z
    have hinv : c⁻¹ (ee z) = d z 0 := by
      rw [← hce]
      simp
    rw [hinv]
    change c ((d x * d z) 0) = standardD8 x (ee z)
    rw [← map_mul]
    change c (d (x * z) 0) = (standardD8 x * standardD8 z) 0
    rw [← map_mul]
    exact hc (x * z)
  refine ⟨c, ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    change MulAut.conj c (d z) ∈ twoGroup
    rw [hconj]
    exact standardD8_range ▸ ⟨z, rfl⟩
  · rw [← standardD8_range]
    rintro _ ⟨x, rfl⟩
    refine ⟨d x, ⟨x, rfl⟩, hconj x⟩


end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
