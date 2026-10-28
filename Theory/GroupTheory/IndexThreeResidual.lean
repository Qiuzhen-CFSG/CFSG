module

public import Theory.GroupTheory.PResidual.PrimeSetPerfect
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Finite.Perm

/-!
# Residuals in an index-three local product

The three-coset action places O^{2,3}(G) in every subgroup of index three.
If the normal two-perfect subgroups there are trivial or have cubic
quotient over their two-core, G is a {2,3}-group. Its prime-to-three
residual is then supplemented by the original Sylow two-subgroup.

The normal-intersection theorem retains the literal inclusion maps:
when L=O^{p′}(M), the embedded residuals of C and C∩L agree for C≤M.
These results supply the residual and product steps of Aschbacher–Smith
13.4.8, printed p.905, using the earlier 13.3.9 conclusion, printed p.887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem twoThree_of_two_group {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 2 A) : IsPiGroup twoThreePrimes A := by
  rw [IsPiGroup_iff]
  intro p hp
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hd : p.val ∣ 2 := p.property.dvd_of_dvd_pow (hn ▸ hp)
  exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left p.property.ne_one)

theorem twoThreeResidual_le_of_index_three (M : Subgroup G) (hi : M.index = 3) :
    piResidual twoThreePrimes G ≤ M := by
  let f : G →* Equiv.Perm (G ⧸ M) := MulAction.toPermHom G (G ⧸ M)
  have hcard : Nat.card (Equiv.Perm (G ⧸ M)) = 6 := by
    rw [Nat.card_perm, ← index_eq_card, hi]
    decide
  have hp : IsPiGroup twoThreePrimes (Equiv.Perm (G ⧸ M)) := by
    rw [IsPiGroup_iff]
    intro p hd
    rw [hcard] at hd
    change p.val = 2 ∨ p.val = 3
    have hd' : p.val ∣ 2 * 3 := hd
    rcases p.property.dvd_mul.mp hd' with hd2 | hd3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hd3 |>.resolve_left p.property.ne_one)
  have hr : piResidual twoThreePrimes G ≤ f.ker :=
    piResidual_le_ker_of_range twoThreePrimes f (hp.of_injective f.range.subtype f.range.subtype_injective)
  exact hr.trans (M.normalCore_eq_ker.symm ▸ M.normalCore_le)

theorem twoThree_of_index_three_normal_twoPerfect (M : Subgroup G) (hi : M.index = 3)
    (hlocal : ∀ Y : Subgroup G, Y.Normal → Y ≤ M → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3) : IsPiGroup twoThreePrimes G := by
  let R := piResidual twoThreePrimes G
  have hperfect : IsPPerfect 2 R := by
    intro N hN hp
    let := hN
    exact isPiPerfect_piResidual twoThreePrimes N hN (twoThree_of_two_group hp)
  have hRpi : IsPiGroup twoThreePrimes R := by
    rcases hlocal R inferInstance (twoThreeResidual_le_of_index_three M hi) hperfect with hr | hr
    · rw [hr, IsPiGroup_iff]
      intro p hp
      rw [card_bot] at hp
      exact (p.property.not_dvd_one hp).elim
    · apply IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 R)
        ((twoThree_of_two_group pCore_isPGroup).isPiSubgroup _)
      rw [IsPiGroup_iff]
      intro p hp
      rw [hr] at hp
      exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
  exact IsPiGroup.of_normal_subgroup_and_quotient R (hRpi.isPiSubgroup _)
    (isPiGroup_quotient_piResidual twoThreePrimes)

end Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem primeToResidual_three_sup_sylow_of_twoThree
    (hG : IsPiGroup twoThreePrimes G) (T : Sylow 2 G) :
    primeToResidual 3 G ⊔ (T : Subgroup G) = ⊤ := by
  rw [← twoResidual_eq_primeToResidual_three hG]
  exact pResidual_sup_sylow_eq_top T
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem embedded_primeToResidual_intersection_of_le (p : ℕ) [Fact p.Prime]
    (M L C : Subgroup G) (hCM : C ≤ M)
    (hL : (primeToResidual p M).map M.subtype = L) :
    (primeToResidual p C).map C.subtype =
      (primeToResidual p (L ⊓ C : Subgroup G)).map (L ⊓ C).subtype := by
  have hnL : M ≤ normalizer (L : Set G) := by
    rw [← hL]
    have hh := (map_mono (show (⊤ : Subgroup M) ≤ normalizer (primeToResidual p M : Set M)
      from le_normalizer_of_normal)).trans ((primeToResidual p M).le_normalizer_map M.subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  let N := L.subgroupOf C
  let : N.Normal := by
    constructor
    intro a ha c
    exact le_normalizer_iff.mp (hCM.trans hnL) c.val c.property a.val ha
  have hres : primeToResidual p C ≤ N := by
    intro x hx
    have hh := embedded_primeToResidual_mono p hCM (mem_map_of_mem C.subtype hx)
    rwa [hL] at hh
  have he := congrArg (Subgroup.map C.subtype) (embedded_primeToResidual_eq_of_normal p N hres)
  rw [map_embedded_primeToResidual_of_hom p N C.subtype, subgroupOf_map_subtype] at he
  exact he.symm
end Subgroup
