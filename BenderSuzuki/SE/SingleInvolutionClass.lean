module

public import BenderSuzuki.SE.SimpleOddCore

/-!
# Odd subgroups with a single involution class in their normalizer

A proper subgroup with one involution class is strongly embedded if it
contains the full centralizer of a representative. Indeed, an involution in
an intersection of two conjugates gives, after conjugating both occurrences
to the representative, an element of that centralizer. The original
conjugator therefore belongs to the subgroup.

For the normalizer of an odd-order subgroup in a finite simple group,
`SE.SimpleOddCore` excludes strong embedding. The normalizer is consequently
the whole group, and simplicity forces the odd subgroup to be trivial.

Source: the alternative strong-embedding argument in Alperin--Brauer--
Gorenstein, III.7 Proposition 8, article p.110, and Bender--Suzuki Theorem SE.
-/

namespace BenderSuzuki
open PFAppendixIII PFchapter1section1

/-- One involution class and its full centralizer suffice for strong embedding. -/
public theorem isStronglyEmbedded_of_single_involution_class
    {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hM : M ≠ ⊤) (x : G) (hx : orderOf x = 2)
    (hxM : x ∈ M) (hC : Subgroup.centralizer ({x} : Set G) ≤ M)
    (hclass : ∀ y ∈ M, orderOf y = 2 →
      ∃ m ∈ M, m * x * m⁻¹ = y) :
    IsStronglyEmbedded M := by
  have hxI : IsInvolution x :=
    ⟨fun h => by simp [h] at hx, by simpa [hx] using pow_orderOf_eq_one x⟩
  refine ⟨hM, ⟨x, hxM, hxI⟩, ?_⟩
  intro g hg y hyM hyg hyI
  have hy : orderOf y = 2 := orderOf_eq_prime hyI.sq_eq_one hyI.ne_one
  obtain ⟨m, hm, hmx⟩ := hclass y hyM hy
  have hzM : g * y * g⁻¹ ∈ M := by
    have h := rightConjugateElem_mem_of_mem_rightConjugate
      (g := g⁻¹) (by simpa using hyg)
    simpa [rightConjugateElem] using h
  have hz : orderOf (g * y * g⁻¹) = 2 :=
    ((MulAut.conj g).orderOf_eq y).trans hy
  obtain ⟨n, hn, hnx⟩ := hclass (g * y * g⁻¹) hzM hz
  let c := n⁻¹ * g * m
  have hcfix : c * x * c⁻¹ = x := by
    calc
      c * x * c⁻¹ = n⁻¹ * (g * (m * x * m⁻¹) * g⁻¹) * n := by
        dsimp [c]; group
      _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [hmx, ← hnx]
      _ = x := by group
  have hcM : c ∈ M := hC (Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hcfix))
  have hgM : g ∈ M := by
    have h := M.mul_mem (M.mul_mem hn hcM) (M.inv_mem hm)
    simpa [c, mul_assoc] using h
  exact hg hgM

/-- An odd subgroup vanishes if its normalizer has a single involution class
and contains the full centralizer of a representative. -/
public theorem odd_subgroup_eq_bot_of_normalizer_single_involution_class
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (R : Subgroup G) (hR : Odd (Nat.card R))
    (x : G) (hx : orderOf x = 2)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hclass : ∀ y ∈ Subgroup.normalizer (R : Set G), orderOf y = 2 →
      ∃ m ∈ Subgroup.normalizer (R : Set G), m * x * m⁻¹ = y) :
    R = ⊥ := by
  have hxM : x ∈ Subgroup.normalizer (R : Set G) :=
    hC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hM : Subgroup.normalizer (R : Set G) = ⊤ := by
    by_contra hproper
    exact not_isStronglyEmbedded_normalizer_of_odd R hR
      (isStronglyEmbedded_of_single_involution_class _ hproper x hx hxM hC hclass)
  have hnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R hnormal with hbot | htop
  · exact hbot
  · have hxR : x ∈ R := by rw [htop]; exact Subgroup.mem_top x
    have hdiv : 2 ∣ Nat.card R := hx ▸ R.orderOf_dvd_natCard hxR
    exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
      (Nat.coprime_two_left.mpr hR)) hdiv)

end BenderSuzuki
