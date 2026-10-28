module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.OrbitTools
import Mathlib.Tactic.Group

/-!
# Closing a Held class under a cyclic centralizer and one generator

Source: the literal generators and relators of HeG1-P1.M in the retained
HeG1-p2058B0 carrier. Conjugation by powers of `ab` preserves the normalized
relation test. Closure under `a` and `ab` covers the entire conjugacy class.
-/

@[expose] public section

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

def row {ι : Type*} (reps : ι → He) (i : ι) (j : Fin 17) : He :=
  MulAut.conj ((a * b) ^ j.val) (reps i)

theorem row_next {ι : Type*} (reps : ι → He) (i : ι) (j : Fin 17) :
    (a * b) * row reps i j * (a * b)⁻¹ =
      row reps i ⟨(j.val + 1) % 17, Nat.mod_lt _ (by decide)⟩ := by
  have hp : (a * b) ^ ((j.val + 1) % 17) = (a * b) ^ (j.val + 1) := by
    simpa only [orderOf_ab] using pow_mod_orderOf (a * b) (j.val + 1)
  simp only [row, MulAut.conj_apply, hp, pow_succ', mul_inv_rev, mul_assoc]

theorem conjugate_relations {ι : Type*} (reps : ι → He)
    (i : ι) (j : Fin 17) (k : Fin 17)
    (hr : ∀ r : Fin 7, relationWord (row reps i j)
      (row reps i j * (a * b) ^ k.val) r = 1) :
    ∀ r : Fin 7, relationWord (reps i) (reps i * (a * b) ^ k.val) r = 1 := by
  let f := MulAut.conj ((a * b) ^ j.val)
  have hfix : f ((a * b) ^ k.val) = (a * b) ^ k.val := by
    change (a * b) ^ j.val * (a * b) ^ k.val * ((a * b) ^ j.val)⁻¹ = _
    rw [(Commute.pow_pow_self (a * b) j.val k.val).eq, mul_inv_cancel_right]
  intro r
  apply f.injective
  rw [map_one]
  change f.toMonoidHom (relationWord _ _ _) = 1
  rw [map_relationWord, map_mul]
  change relationWord (f (reps i)) (f (reps i) * f ((a * b) ^ k.val)) r = 1
  rw [hfix]
  exact hr r

theorem calculation_of_orbit_representatives {ι : Type*} (reps : ι → He)
    (hseed : ∃ i, reps i = secondSeed)
    (ha : ∀ (i : ι) (j : Fin 17), ∃ (i' : ι) (j' : Fin 17),
      ∀ t : Fin 4,
        representation (a * row reps i j * a⁻¹) ⟨t.val, by omega⟩ =
        representation (row reps i' j') ⟨t.val, by omega⟩)
    (hreject : ∀ (i : ι) (k : Fin 17), k = 1 ∨ k = 3 →
      ∃ (r : Fin 7) (p : Fin 2058),
        representation (relationWord (reps i) (reps i * (a * b) ^ k.val) r) p ≠ p) :
    ClassCalculation secondSeed := by
  have ha' : ∀ v : ι × Fin 17, ∃ w : ι × Fin 17,
      a * row reps v.1 v.2 * a⁻¹ = row reps w.1 w.2 := by
    rintro ⟨i, j⟩
    obtain ⟨i', j', hij⟩ := ha i j
    exact ⟨(i', j'), eq_of_four_point_images hij⟩
  apply classCalculation_of_closed_family (fun v : ι × Fin 17 => row reps v.1 v.2)
  · obtain ⟨i, hi⟩ := hseed
    exact ⟨(i, 0), by simpa only [row, Fin.val_zero, pow_zero, MulAut.conj_apply,
      one_mul, inv_one, mul_one] using hi.symm⟩
  · exact ha'
  · rintro ⟨i, j⟩
    let j' : Fin 17 := ⟨(j.val + 1) % 17, Nat.mod_lt _ (by decide)⟩
    obtain ⟨w, hw⟩ := ha' (i, j')
    refine ⟨w, ?_⟩
    have hba : a * (a * b) = b := by
      rw [← mul_assoc, ← pow_two, a_sq, one_mul]
    rw [← row_next reps i j] at hw
    have he : a * ((a * b) * row reps i j * (a * b)⁻¹) * a⁻¹ =
        b * row reps i j * b⁻¹ := by
      calc
        _ = (a * (a * b)) * row reps i j * (a * (a * b))⁻¹ := by group
        _ = _ := by rw [hba]
    exact he.symm.trans hw
  · rintro k hk ⟨i, j⟩ hr
    obtain ⟨r, p, hp⟩ := hreject i k hk
    have h := conjugate_relations reps i j k hr r
    exact (hp (by rw [h, map_one]; rfl)).elim

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
