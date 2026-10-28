module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Sylow
public import Theory.GroupTheory.TwoThreeSolvable
import Mathlib.Tactic

/-!
# Solvability and generation of the two partition stabilizers

These are the actual stabilizers of the four-plus-three partition and the
three-pair partition of seven points. Their orders, 144 and 48, imply
solvability by the proved two-prime theorem. For generation, products of powers
of `(0 1 2)` and `(4 5 6)` give nine distinct cosets of the common subgroup of
order sixteen. Powers of `(0 2 4)(1 3 5)` give three distinct cosets in the
pair stabilizer. The known orders make these lists exhaustive. All these
cycles are even, so the same decompositions restrict to any `B` containing A₇.
Only the small coset-separation and cycle checks use kernel-checked evaluation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
private def cycle012 : S7 := swap 0 1 * swap 1 2
private def cycle456 : S7 := swap 4 5 * swap 5 6
private def pairCycle : S7 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)
private theorem cycle012_order : orderOf cycle012 = 3 := by
  apply orderOf_eq_prime_iff.mpr
  decide +kernel
private theorem cycle012_mem : cycle012 ∈ fourThreeStabilizer ∧ cycle012 ∈ alternatingGroup (Fin 7) := by decide +kernel
private theorem cycle456_mem : cycle456 ∈ fourThreeStabilizer ∧ cycle456 ∈ alternatingGroup (Fin 7) := by decide +kernel
private theorem pairCycle_mem : pairCycle ∈ pairStabilizer ∧ pairCycle ∈ alternatingGroup (Fin 7) := by decide +kernel
private theorem cover_of_card {ι : Type*} (R : Subgroup S7)
    (hT : standardTwo ≤ R) (w : ι → S7) (hw : ∀ i, w i ∈ R)
    (hsep : ∀ i j, (w i)⁻¹ * w j ∈ standardTwo → i = j)
    (hcard : Nat.card ι * 16 = Nat.card R) :
    ∀ g ∈ R, ∃ i, (w i)⁻¹ * g ∈ standardTwo := by
  let f : ι × standardTwo → R := fun p =>
    ⟨w p.1 * p.2.val, R.mul_mem (hw p.1) (hT p.2.property)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, t⟩ ⟨j, u⟩ he
    have he' : w i * t.val = w j * u.val := congrArg Subtype.val he
    have hdiff : (w i)⁻¹ * w j = t.val * u.val⁻¹ := by
      calc
        _ = (w i)⁻¹ * (w j * u.val) * u.val⁻¹ := by group
        _ = _ := by rw [← he']; group
    have hij : i = j := hsep i j (by
      rw [hdiff]
      exact standardTwo.mul_mem t.property (standardTwo.inv_mem u.property))
    subst j
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel he'))
  have hc : Nat.card (ι × standardTwo) = Nat.card R := by
    rw [Nat.card_prod, standardTwo_card]
    exact hcard
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2
  intro g hg
  obtain ⟨⟨i, t⟩, ht⟩ := hs ⟨g, hg⟩
  have he : w i * t.val = g := congrArg Subtype.val ht
  refine ⟨i, ?_⟩
  rw [← he, inv_mul_cancel_left]
  exact t.property

private theorem four_cover : ∀ p : FourThree, ∃ i j : Fin 3,
    (cycle012 ^ i.val * cycle456 ^ j.val)⁻¹ * fourThreeHom p ∈ standardTwo := by
  have h := cover_of_card fourThreeStabilizer inf_le_left
    (fun ij : Fin 3 × Fin 3 => cycle012 ^ ij.1.val * cycle456 ^ ij.2.val)
    (fun ij => fourThreeStabilizer.mul_mem
      (fourThreeStabilizer.pow_mem cycle012_mem.1 _) (fourThreeStabilizer.pow_mem cycle456_mem.1 _))
    (by decide +kernel)
    (by rw [Nat.card_prod, Nat.card_fin, fourThreeStabilizer_card])
  intro p
  obtain ⟨⟨i, j⟩, hij⟩ := h (fourThreeHom p) ⟨p, rfl⟩
  exact ⟨i, j, hij⟩

private theorem pair_cover : ∀ g : S7, g ∈ pairStabilizer → ∃ i : Fin 3,
    (pairCycle ^ i.val)⁻¹ * g ∈ standardTwo := by
  exact cover_of_card pairStabilizer inf_le_right (fun i : Fin 3 => pairCycle ^ i.val)
    (fun i => pairStabilizer.pow_mem pairCycle_mem.1 _)
    (by decide +kernel)
    (by rw [Nat.card_fin, pairStabilizer_card])

private theorem solvable_card_dvd_144 (G : Type*) [Group G] [Finite G]
    (hd : Nat.card G ∣ 144) : Group.IsSolvable G := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  have h : p ∣ 2 ^ 4 * 3 ^ 2 := hpd.trans hd
  simpa only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 4 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] using h

/-- Solvability of the actual four-plus-three stabilizer restricted to `B`. -/
theorem fourThreeStabilizer_comap_isSolvable (B : Subgroup S7) :
    Group.IsSolvable (fourThreeStabilizer.comap B.subtype) := by
  apply solvable_card_dvd_144
  simpa only [fourThreeStabilizer_card] using
    card_comap_dvd_of_injective fourThreeStabilizer B.subtype B.subtype_injective
/-- Solvability of the actual three-pair stabilizer restricted to `B`. -/
theorem pairStabilizer_comap_isSolvable (B : Subgroup S7) :
    Group.IsSolvable (pairStabilizer.comap B.subtype) := by
  apply solvable_card_dvd_144
  have h := card_comap_dvd_of_injective pairStabilizer B.subtype B.subtype_injective
  rw [pairStabilizer_card] at h
  exact h.trans (by decide : 48 ∣ 144)

private theorem comap_le_of_transversal {ι : Type*} (B R : Subgroup S7)
    (C : Subgroup B) (hT : standardTwoIn B ≤ C) (w : ι → B)
    (hw : ∀ i, w i ∈ C)
    (hcover : ∀ g ∈ R, ∃ i, ((w i : B) : S7)⁻¹ * g ∈ standardTwo) :
    R.comap B.subtype ≤ C := by
  intro g hg
  obtain ⟨i, hi⟩ := hcover g hg
  have ht : (w i)⁻¹ * g ∈ standardTwoIn B := hi
  have h := C.mul_mem (hw i) (hT ht)
  simpa only [mul_inv_cancel_left] using h

private theorem cycle456_order : orderOf cycle456 = 3 := by
  apply orderOf_eq_prime_iff.mpr
  decide +kernel
private theorem pairCycle_order : orderOf pairCycle = 3 := by
  apply orderOf_eq_prime_iff.mpr
  decide +kernel

/-- The four-plus-three stabilizer is generated by its elements of order three
and the standard Sylow two-subgroup. -/
theorem fourThreeStabilizer_comap_eq_closure_three_sup_standardTwo
    (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    fourThreeStabilizer.comap B.subtype =
      Subgroup.closure {g : B | g ∈ fourThreeStabilizer.comap B.subtype ∧ orderOf g = 3} ⊔
        standardTwoIn B := by
  let C := Subgroup.closure
    {g : B | g ∈ fourThreeStabilizer.comap B.subtype ∧ orderOf g = 3} ⊔ standardTwoIn B
  let aB : B := ⟨cycle012, hB cycle012_mem.2⟩
  let bB : B := ⟨cycle456, hB cycle456_mem.2⟩
  have ha : aB ∈ C := Subgroup.mem_sup_left (Subgroup.subset_closure
    ⟨cycle012_mem.1, by rw [← Subgroup.orderOf_coe]; exact cycle012_order⟩)
  have hb : bB ∈ C := Subgroup.mem_sup_left (Subgroup.subset_closure
    ⟨cycle456_mem.1, by rw [← Subgroup.orderOf_coe]; exact cycle456_order⟩)
  apply le_antisymm
  · apply comap_le_of_transversal B fourThreeStabilizer C le_sup_right
      (fun ij : Fin 3 × Fin 3 => aB ^ ij.1.val * bB ^ ij.2.val)
      (fun ij => C.mul_mem (C.pow_mem ha _) (C.pow_mem hb _))
    rintro g ⟨p, rfl⟩
    obtain ⟨i, j, hij⟩ := four_cover p
    exact ⟨(i, j), hij⟩
  · apply sup_le
    · exact (Subgroup.closure_le _).mpr (fun _ hg => hg.1)
    · exact Subgroup.comap_mono inf_le_left

/-- The three-pair stabilizer is generated by its elements of order three
and the standard Sylow two-subgroup. -/
theorem pairStabilizer_comap_eq_closure_three_sup_standardTwo
    (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    pairStabilizer.comap B.subtype =
      Subgroup.closure {g : B | g ∈ pairStabilizer.comap B.subtype ∧ orderOf g = 3} ⊔
        standardTwoIn B := by
  let C := Subgroup.closure
    {g : B | g ∈ pairStabilizer.comap B.subtype ∧ orderOf g = 3} ⊔ standardTwoIn B
  let cB : B := ⟨pairCycle, hB pairCycle_mem.2⟩
  have hc : cB ∈ C := Subgroup.mem_sup_left (Subgroup.subset_closure
    ⟨pairCycle_mem.1, by rw [← Subgroup.orderOf_coe]; exact pairCycle_order⟩)
  apply le_antisymm
  · apply comap_le_of_transversal B pairStabilizer C le_sup_right
      (fun i : Fin 3 => cB ^ i.val) (fun i => C.pow_mem hc _)
    intro g hg
    exact pair_cover g hg
  · apply sup_le
    · exact (Subgroup.closure_le _).mpr (fun _ hg => hg.1)
    · exact Subgroup.comap_mono inf_le_right

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
