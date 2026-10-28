module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.TorusCriterion
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Product tori and independent inversion

The two copies of SL₂ act on the two orthogonal hyperbolic planes in the
ordered-half convention of the actual symplectic matrix group. A faithful
product of two cyclic groups, with index prime to r and independent
inversion of its first factor, contains an inverted Sylow r-subgroup.
Central commutator pairing and transfer then exclude r from a perfect
central kernel. Neither the embedding nor the transfer argument assumes
characteristic two.

Source: the torus-transfer argument for Aschbacher–Smith I.1.1–4,
printed pp.407–408, and GLS3 §6.1. The matrix embedding and generator
calculation extend `CentralCovers.OddPrimary.Nonsplit`.
-/

open Matrix Subgroup
open scoped IsMulCommutative

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining
namespace ProductTori

section Planes
variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F

private def pairMatrix (A B : SL) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![A 0 0, 0; 0, B 0 0] !![A 0 1, 0; 0, B 0 1]
    !![A 1 0, 0; 0, B 1 0] !![A 1 1, 0; 0, B 1 1]

private theorem pairMatrix_mem (A B : SL) : pairMatrix A B ∈ Matrix.symplecticGroup (Fin 2) F := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.property
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [det_fin_two] using B.property
  rw [pairMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, mul_comm, hA, hB]

public def pairHom : (SL × SL) →* Sp F where
  toFun A := ⟨pairMatrix A.1 A.2, pairMatrix_mem A.1 A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change pairMatrix (A.1 * B.1) (A.2 * B.2) = pairMatrix A.1 A.2 * pairMatrix B.1 B.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

public theorem pairHom_injective : Function.Injective (pairHom (F := F)) := by
  intro A B h
  have he (x y : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val x y) h
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 0) (.inl 0)
    · exact he (.inl 0) (.inr 0)
    · exact he (.inr 0) (.inl 0)
    · exact he (.inr 0) (.inr 0)
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 1) (.inl 1)
    · exact he (.inl 1) (.inr 1)
    · exact he (.inr 1) (.inl 1)
    · exact he (.inr 1) (.inr 1)

end Planes

/-- A product torus of index prime to r contains the required inverted Sylow. -/
public theorem exists_inverted_sylow_of_product_index
    {G C : Type*} [Group G] [Finite G] [CommGroup C] [Finite C] [IsCyclic C]
    {p : ℕ} [Fact p.Prime]
    (ι : C × C →* G) (hι : Function.Injective ι)
    (hpindex : ¬ p ∣ ι.range.index) (w : G)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c)) :
    ∃ P : Sylow p G, Nonempty (PerfectCentralCovering.InvertedGenerators (P : Subgroup G)) := by
  classical
  have hp : p.Prime := Fact.out
  let R : Sylow p C := default
  let D : Subgroup (C × C) := (R : Subgroup C).prod (R : Subgroup C)
  have hDp : IsPGroup p D := by
    obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m+m)
    rw [Nat.card_congr (Subgroup.prodEquiv (R : Subgroup C) (R : Subgroup C)).toEquiv,
      Nat.card_prod, hm, pow_add]
  let Q : Subgroup (G) := D.map ι
  have hQp : IsPGroup p Q := hDp.map ι
  have hQi : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_of_injective _ hι, Subgroup.index_prod]
    exact hp.not_dvd_mul (hp.not_dvd_mul R.not_dvd_index R.not_dvd_index) hpindex
  let P : Sylow p (G) := hQp.toSylow hQi
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := R)
  have hx : ι ((a : C),1) ∈ Q := ⟨((a : C),1), ⟨a.property, (R : Subgroup C).one_mem⟩, rfl⟩
  have hy : ι (1,(a : C)) ∈ Q := ⟨(1,(a : C)), ⟨(R : Subgroup C).one_mem, a.property⟩, rfl⟩
  refine ⟨P, ⟨{
    left := ⟨ι ((a : C),1), hx⟩
    right := ⟨ι (1,(a : C)), hy⟩
    commute := (Commute.all ((a : C),1) (1,(a : C))).map ι
    normalForm := ?_
    inverter := w
    invert_left := (hinv a).trans (by
      simpa only [Prod.inv_mk, inv_one] using ι.map_inv ((a : C),1))
    fix_right := hfix a }⟩⟩
  intro z
  obtain ⟨⟨c,d⟩, hcd, he⟩ := z.property
  change c ∈ (R : Subgroup C) ∧ d ∈ (R : Subgroup C) at hcd
  obtain ⟨i, hi⟩ := ha ⟨c, hcd.1⟩
  obtain ⟨j, hj⟩ := ha ⟨d, hcd.2⟩
  refine ⟨i, j, ?_⟩
  change (z : G) = ι ((a : C),1)^i * ι (1,(a : C))^j
  rw [← he, ← map_zpow, ← map_zpow, ← map_mul]
  apply congrArg ι
  apply Prod.ext
  · simpa using (congrArg (fun x : R => (x : C)) hi).symm
  · simpa using (congrArg (fun x : R => (x : C)) hj).symm

/-- The product-torus criterion applied to the literal perfect central cover. -/
public theorem not_dvd_card_kernel_of_product_index
    {E G C : Type*} [Group E] [Finite E] [Group G] [Finite G]
    [CommGroup C] [Finite C] [IsCyclic C]
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (ι : C × C →* G) (hι : Function.Injective ι)
    (hi : ¬ r ∣ ι.range.index) (w : G)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c))
    (f : PerfectCentralCovering.Cover E G) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let := f.isPerfect
  obtain ⟨P, ⟨hP⟩⟩ := exists_inverted_sylow_of_product_index ι hι hi w hinv hfix
  exact PerfectCentralCovering.not_dvd_card_kernel_of_inverted_sylow hr2 P hP
    f.toMonoidHom f.surjective f.ker_le_center

end ProductTori
end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining
