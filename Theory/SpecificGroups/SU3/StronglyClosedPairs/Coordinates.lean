module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Residual

/-!
# Torus fusion of commuting factors in a Hermitian root group

The root group has coordinates `(a,b)` with `b + conj b + a * conj a = 0`.
Its commuting condition is `a * conj c = c * conj a`. A norm-one torus
element whose cube is nontrivial acts on `a` by a scalar outside the fixed
field. If a commuting factor union is invariant under this action, one
factor must have first coordinate zero.

The smaller factor has first coordinate zero and therefore square one.
The full torus is transitive on nonidentity elements of this central layer.
If the other factor has a noncentral element, its torus conjugates stay in
that factor, and their squares cover the central layer. If both factors
are central, the subgroup-in-a-union lemma proves nesting. This controls
whole factors without requiring torus transitivity on first coordinates.

This is the coordinate argument for the PSU₃ case of the terminal step of
Aschbacher, *On finite groups of component type* (1975), Lemma 3.4, p.96.
The actual projective root maps and torus formulas are Huppert II.10.12.
-/

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs.Coordinates
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def centralLayer : Subgroup (hermitianUnipotentCoord J) where
  carrier := {z | z.val.1 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro z w hz hw
    change z.val.1 + w.val.1 = 0
    rw [hz, hw, add_zero]
  inv_mem' := by
    intro z hz
    change -z.val.1 = 0
    rw [hz, neg_zero]

private theorem commute_iff (z w : hermitianUnipotentCoord J) :
    Commute z w ↔ z.val.1 * J.conj w.val.1 = w.val.1 * J.conj z.val.1 := by
  constructor
  · intro h
    have he := congrArg (fun u : hermitianUnipotentCoord J => u.val.2) h.eq
    change z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1 =
      w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 at he
    linear_combination -he
  · intro h
    show z * w = w * z
    apply Subtype.ext
    apply Prod.ext
    · exact add_comm _ _
    · change z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1 =
        w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1
      rw [h, add_comm]

private theorem cube_not_fixed [CharP E 2] (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E)^3 ≠ 1) :
    J.conj ((k : E)^3) ≠ (k : E)^3 := by
  intro he
  have hinv : ((k : E)^3)⁻¹ = (k : E)^3 := by
    simpa only [map_pow, hk, inv_pow] using he
  have hsq : ((k : E)^3)^2 = 1 := by
    rw [pow_two]
    calc
      _ = ((k : E)^3)⁻¹ * (k : E)^3 := by rw [hinv]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero k))
  apply hk3
  have hh : ((k : E)^3 - 1)^2 = 0 := by
    calc
      ((k : E)^3 - 1)^2 = ((k : E)^3)^2 - 1 := by
        simp only [CharTwo.sub_eq_add, CharTwo.add_sq, one_pow]
      _ = 0 := by rw [hsq]; ring
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)

private theorem commute_action_obstruction [CharP E 2] (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E)^3 ≠ 1)
    (z w : hermitianUnipotentCoord J) (hz : z.val.1 ≠ 0) (hw : w.val.1 ≠ 0)
    (hzw : Commute z w) : ¬ Commute (hermitianTorusAction J k z) w := by
  intro htw
  have h1 := (commute_iff J z w).mp hzw
  have h2 := (commute_iff J _ w).mp htw
  rw [normOne_action_first J k hk, map_mul] at h2
  have he : (k : E)^3 * (z.val.1 * J.conj w.val.1) =
      J.conj ((k : E)^3) * (z.val.1 * J.conj w.val.1) := by
    calc
      _ = w.val.1 * (J.conj ((k : E)^3) * J.conj z.val.1) := by
        simpa [mul_assoc] using h2
      _ = J.conj ((k : E)^3) * (w.val.1 * J.conj z.val.1) := by ring
      _ = _ := by rw [← h1]
  exact cube_not_fixed J k hk hk3
    ((mul_right_cancel₀ (mul_ne_zero hz ((map_ne_zero J.conj).mpr hw)) he).symm)

private theorem one_factor_first_zero [CharP E 2] (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E)^3 ≠ 1)
    (B C : Subgroup (hermitianUnipotentCoord J))
    (hcomm : ∀ z ∈ B, ∀ w ∈ C, Commute z w)
    (hclosed : ∀ z, z ∈ B ∨ z ∈ C →
      hermitianTorusAction J k z ∈ B ∨ hermitianTorusAction J k z ∈ C) :
    B ≤ centralLayer J ∨ C ≤ centralLayer J := by
  classical
  by_cases hb : B ≤ centralLayer J
  · exact Or.inl hb
  right
  obtain ⟨z, hz, hzb⟩ := Set.not_subset.mp hb
  have hz0 : z.val.1 ≠ 0 := hzb
  intro w hw
  change w.val.1 = 0
  by_contra hw0
  have htB : hermitianTorusAction J k z ∈ B := by
    rcases hclosed z (Or.inl hz) with h | h
    · exact h
    · exact False.elim (commute_action_obstruction J k hk hk3 z z hz0 hz0
        (Commute.refl z) (hcomm z hz _ h).symm)
  exact commute_action_obstruction J k hk hk3 z w hz0 hw0
    (hcomm z hz w hw) (hcomm _ htB w hw)

private theorem action_square (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (k : Eˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z)^2 = hermitianTorusAction J k (z^2) := by
  apply root_injective J hJ
  rw [map_pow, ← projective_torus_action, ← projective_torus_action, map_pow]
  exact (map_pow (MulAut.conj (hermitianTorusPSU J hJ k))
    (hermitianUnipotentPSU J hJ z) 2).symm

private theorem central_fixed [CharP E 2] (z : hermitianUnipotentCoord J)
    (hz : z.val.1 = 0) : J.conj z.val.2 = z.val.2 := by
  have hh := z.property
  rw [hz, zero_mul, add_zero] at hh
  exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)

private theorem central_orbit [Finite E] [CharP E 2] {q : ℕ}
    (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (z w : hermitianUnipotentCoord J)
    (hz : z.val.1 = 0) (hw : w.val.1 = 0) (hz1 : z ≠ 1) (hw1 : w ≠ 1) :
    ∃ k : Eˣ, hermitianTorusAction J k z = w := by
  have hz2 : z.val.2 ≠ 0 := fun h => hz1 (Subtype.ext (Prod.ext hz h))
  have hw2 : w.val.2 ≠ 0 := fun h => hw1 (Subtype.ext (Prod.ext hw h))
  obtain ⟨a, ha, hn⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed
    (z.val.2 / w.val.2) (by rw [map_div₀, central_fixed J z hz, central_fixed J w hw])
    (div_ne_zero hz2 hw2)
  refine ⟨Units.mk0 a ha, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simpa only [hermitianTorusAction_fst, hz, zero_mul] using hw.symm
  · rw [hermitianTorusAction_snd]
    simp only [Units.val_mk0]
    have hna : J.conj a ≠ 0 := (map_ne_zero J.conj).mpr ha
    field_simp at hn ⊢
    linear_combination -hn


private theorem nested_of_first_zero [Finite E] [CharP E 2] {q : ℕ}
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (B C : Subgroup (hermitianUnipotentCoord J)) (hB : B ≤ centralLayer J)
    (hclosed : ∀ (k : Eˣ) z, z ∈ B ∨ z ∈ C →
      hermitianTorusAction J k z ∈ B ∨ hermitianTorusAction J k z ∈ C) :
    B ≤ C ∨ C ≤ B := by
  classical
  by_cases hbot : B = ⊥
  · exact Or.inl (hbot ▸ bot_le)
  by_cases hC : C ≤ centralLayer J
  · obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp hbot
    have hz : (z : hermitianUnipotentCoord J).val.1 = 0 := hB z.property
    have hcover : (centralLayer J : Set (hermitianUnipotentCoord J)) ⊆
        (B : Set _) ∪ C := by
      intro w hw
      by_cases hw1 : w = 1
      · subst w; exact Or.inl B.one_mem
      obtain ⟨k, hk⟩ := central_orbit J hcard hfixed z w hz hw
        (fun he => hz1 (Subtype.ext he)) hw1
      rw [← hk]
      exact hclosed k z (Or.inl z.property)
    rcases SubgroupClass.subset_union.mp hcover with h | h
    · exact Or.inr (hC.trans h)
    · exact Or.inl (hB.trans h)
  · obtain ⟨w, hwC, hw0⟩ := Set.not_subset.mp hC
    have hw : w.val.1 ≠ 0 := hw0
    have hsq0 : (w^2).val.1 = 0 := by rw [square_coordinates]
    have hsq1 : w^2 ≠ 1 := by
      intro he
      have hh := congrArg (fun u : hermitianUnipotentCoord J => u.val.2) he
      rw [show (w^2).val.2 = w.val.1 * J.conj w.val.1 by rw [square_coordinates]] at hh
      exact mul_ne_zero hw ((map_ne_zero J.conj).mpr hw) hh
    have htC (k : Eˣ) : hermitianTorusAction J k w ∈ C := by
      rcases hclosed k w (Or.inr hwC) with h | h
      · have hz : (hermitianTorusAction J k w).val.1 = 0 := hB h
        rw [hermitianTorusAction_fst] at hz
        exact False.elim ((mul_ne_zero (mul_ne_zero hw (Units.ne_zero k))
          (pow_ne_zero _ (inv_ne_zero ((map_ne_zero J.conj).mpr (Units.ne_zero k))))) hz)
      · exact h
    left
    intro z hzB
    by_cases hz1 : z = 1
    · subst z; exact C.one_mem
    obtain ⟨k, hk⟩ := central_orbit J hcard hfixed (w^2) z hsq0 (hB hzB) hsq1 hz1
    have hp := C.pow_mem (htC k) 2
    rwa [action_square J hJ, hk] at hp

private theorem central_square [CharP E 2] (z : hermitianUnipotentCoord J)
    (hz : z ∈ centralLayer J) : z ^ 2 = 1 := by
  apply Subtype.ext
  rw [square_coordinates]
  change (0, z.val.1 * J.conj z.val.1) = (0, 0)
  rw [show z.val.1 = 0 from hz, zero_mul]

/-- Torus fusion makes one commuting factor an elementary subgroup of the other.
The central layer is obtained by the coordinate calculation, not assumed. -/
public theorem factors_nested_elementary [Finite E] [CharP E 2] {q : ℕ}
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (B C : Subgroup (hermitianUnipotentCoord J))
    (hcomm : ∀ z ∈ B, ∀ w ∈ C, Commute z w)
    (hclosed : ∀ (k : Eˣ) z, z ∈ B ∨ z ∈ C →
      hermitianTorusAction J k z ∈ B ∨ hermitianTorusAction J k z ∈ C) :
    (B ≤ C ∧ ∀ z ∈ B, z ^ 2 = 1) ∨
      (C ≤ B ∧ ∀ z ∈ C, z ^ 2 = 1) := by
  obtain ⟨k, _, hk3, _, hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  rcases one_factor_first_zero J k hk hk3 B C hcomm (hclosed k) with hB | hC
  · rcases nested_of_first_zero J hJ hcard hfixed B C hB hclosed with h | h
    · exact Or.inl ⟨h, fun z hz => central_square J z (hB hz)⟩
    · exact Or.inr ⟨h, fun z hz => central_square J z (hB (h hz))⟩
  · rcases nested_of_first_zero J hJ hcard hfixed C B hC
      (fun k z hz => (hclosed k z hz.symm).symm) with h | h
    · exact Or.inr ⟨h, fun z hz => central_square J z (hC hz)⟩
    · exact Or.inl ⟨h, fun z hz => central_square J z (hC (h hz))⟩

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs.Coordinates
