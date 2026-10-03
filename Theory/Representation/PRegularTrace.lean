module
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Simultaneous reduction of character values to p-regular elements

For a finite group and a field of prime characteristic p, each group element
has the same character value as one p-regular element in every finite-dimensional
representation over that field. The choice is made from the group element
alone, before introducing the representation or its vector space. This is
the elementary p-part reduction in modular character theory, used to bound
irreducible families by p-regular conjugacy classes and to count the trace
classes of the standard SL2 representation. Algebraic closure is not required.

Write the element order as p^k times a number prime to p. Its p^k-th power
is p-regular, and powering by p^k is invertible on its cyclic subgroup.
A suitable power h therefore has prime-to-p order and the same p^k-th power
as the original element. In any representation the two operators commute,
so their difference has p^k-th power zero in characteristic p. The trace of
a nilpotent operator is nilpotent, hence zero in the field, giving equality.
The zero vector space is handled separately when installing the endomorphism
ring's characteristic instance. No ordinary character orthogonality is used.
-/

namespace Representation
universe u v w

private theorem exists_pRegular_power
    {G : Type u} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) (g : G) :
    ∃ k a : ℕ, ¬ p ∣ orderOf (g ^ a) ∧ g ^ (p ^ k) = (g ^ a) ^ (p ^ k) := by
  obtain ⟨k, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have horder : orderOf (g ^ (p ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by rw [hn]; exact dvd_mul_right _ _), hn]
    exact Nat.mul_div_cancel_left m (pow_pos hp.pos _)
  have hcop : (p ^ k).Coprime (orderOf (g ^ (p ^ k))) := by
    rw [horder]
    exact (hp.coprime_iff_not_dvd.mpr hm).pow_left k
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨k, p ^ k * b, ?_, ?_⟩
  · intro hd
    apply hm
    rw [pow_mul] at hd
    exact hd.trans ((orderOf_pow_dvd b).trans (horder ▸ dvd_refl _))
  · simpa only [← pow_mul, Nat.mul_assoc, Nat.mul_comm b (p ^ k)] using hb.symm

/-- One p-regular element preserves the character value simultaneously in all representations. -/
public theorem exists_pRegular_same_character
    {G : Type u} [Group G] [Finite G] {F : Type v} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (g : G) :
    ∃ h : G, ¬ p ∣ orderOf h ∧
      ∀ (M : Type w) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
        (ρ : Representation F G M), ρ.character g = ρ.character h := by
  obtain ⟨k, a, hreg, hpow⟩ := exists_pRegular_power p Fact.out g
  refine ⟨g ^ a, hreg, ?_⟩
  intro M _ _ _ ρ
  rcases subsingleton_or_nontrivial M with hM | hM
  · let := hM
    unfold character
    congr 1
    exact Subsingleton.elim _ _
  · let := hM
    let : CharP (Module.End F M) p :=
      charP_of_injective_algebraMap (algebraMap F (Module.End F M)).injective p
    have hcomm : Commute (ρ g) (ρ (g ^ a)) := by
      rw [map_pow]
      exact (Commute.refl (ρ g)).pow_right a
    have hnil : IsNilpotent (ρ g - ρ (g ^ a)) := by
      refine ⟨p ^ k, ?_⟩
      rw [sub_pow_char_pow_of_commute p k hcomm, ← map_pow, ← map_pow, hpow, sub_self]
    have htrace := (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    simpa only [map_sub, sub_eq_zero, character] using htrace

end Representation
