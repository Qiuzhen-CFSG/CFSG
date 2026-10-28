module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# An elementary plane from a prime commutator and cyclic fixed subgroup

A two-group acts coprimely on a finite odd p-group R of exponent p.
If the commutator has order p and one actor has cyclic centralizer,
then the common fixed subgroup has order at most p. Coprime generation
bounds |R| by p². Noncyclicity forces equality, and a group of prime-square
order is abelian, so R is elementary abelian.

This is the nonabelian-branch exclusion in Aschbacher–Smith 14.5.11,
printed pp.1015–1016, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Coprime generation identifies the original odd subgroup as an elementary plane. -/
theorem elementary_plane_of_prime_commutator_cyclic_fixed
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (R B : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hB : IsPGroup 2 B)
    (hexp : Monoid.exponent R ∣ p) (hncyc : ¬ IsCyclic R)
    (t : G) (ht : t ∈ B)
    (hcyc : IsCyclic (R ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hm : Nat.card (⁅R,B⁆ : Subgroup G) = p) :
    Nat.card R = p ^ 2 ∧ IsElementaryAbelian p R := by
  let C := R ⊓ centralizer (B : Set G)
  have hCt : C ≤ R ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr ht))
  let : IsCyclic (R ⊓ centralizer ({t} : Set G) : Subgroup G) := hcyc
  let : IsCyclic C := isCyclic_of_injective (inclusion hCt) (inclusion_injective _)
  have hc : Nat.card C ≤ p := by
    have hd := (Monoid.exponent_dvd_of_monoidHom
      (inclusion (show C ≤ R from inf_le_left)) (inclusion_injective _)).trans hexp
    rw [IsCyclic.exponent_eq_card] at hd
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos hd
  let : Group.IsNilpotent R := hR.isNilpotent
  have hs := eq_commutator_sup_centralizer_of_solvable_coprime R B
    le_normalizer_of_normal (inferInstance : Group.IsSolvable R)
    (IsPGroup.coprime_card_of_ne 2 p hp.symm B R hB hR)
  have hn : C ≤ normalizer ((⁅R,B⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (normalizer_commutator_ge_left R B)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes ⁅R,B⁆ C hn
  change Nat.card (⁅R,B⁆ : Subgroup G) * Nat.card C =
    Nat.card (⁅R,B⁆ ⊓ C : Subgroup G) * Nat.card (⁅R,B⁆ ⊔ C : Subgroup G) at hprod
  change R = ⁅R,B⁆ ⊔ C at hs
  rw [←hs,hm] at hprod
  have hsmall : Nat.card R ≤ p ^ 2 := by
    have hpos : 0 < Nat.card (⁅R,B⁆ ⊓ C : Subgroup G) := Nat.card_pos
    have hle : Nat.card R ≤ Nat.card (⁅R,B⁆ ⊓ C : Subgroup G) * Nat.card R :=
      Nat.le_mul_of_pos_left _ hpos
    rw [←hprod] at hle
    exact hle.trans (by nlinarith)
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  have hnle : n ≤ 2 := by
    rw [hn] at hsmall
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hsmall
  have hcard : Nat.card R = p ^ 2 := by
    interval_cases n
    · exact False.elim (hncyc (isCyclic_of_card_dvd_prime (p := p) (by rw [hn]; simp)))
    · exact False.elim (hncyc (isCyclic_of_card_dvd_prime (p := p) (by rw [hn]; simp)))
    · exact hn
  refine ⟨hcard, ?_⟩
  exact {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
    exponent_dvd_p := hexp
  }
end Theory.GroupTheory
