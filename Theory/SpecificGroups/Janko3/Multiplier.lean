module

public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.SpecificGroups.Janko3.Multiplier.Assembly
public import Theory.SpecificGroups.Janko3.Multiplier.ThreePrimaryReduction
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Covering

/-!
# Odd-primary central kernels over the concrete J₃ model

The model in this file is the degree-6156 ATLAS permutation group from
`Sporadic.Janko3.Model`.  Its checked order is
`2^7 * 3^5 * 5 * 17 * 19`.  Thus every Sylow subgroup at an odd prime other
than `3` is cyclic: the prime occurs to the first power in the model order.
The cyclic-Sylow transfer theorem for perfect central extensions then excludes
that prime from every finite perfect central kernel.

This is the source-domain odd-primary part of Aschbacher--Smith I.1.4(2),
printed p.408.  It is deliberately stated for the actual permutation model;
the source assembly supplies a genuine equivalence from its quasisimple
cover to this model.  The remaining two-primary exclusion, 3-primary upper
bound, and construction of a perfect central triple cover are explicit inputs
to the conditional exact-multiplier assembly below. The three-primary reduction
now uses a checked order-243 subgroup with a marked generating pair and cubic
relations; its central-extension calculation remains an explicit input.
-/

namespace Sporadic.Janko3

universe u

open Subgroup
open PerfectCentralCovering
open Theory.GroupTheory

private theorem model_card_factorization :
    Nat.card Model = 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19 := by
  rw [model_card]
  norm_num

private theorem sylow_cyclic_of_odd_prime_ne_three
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (P : Sylow p Model) : IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  by_cases hnle : n ≤ 1
  · apply isCyclic_of_card_dvd_prime (p := p)
    rw [hn]
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : n = 1 := by omega
      simp [hn1]
  · have hn2 : 2 ≤ n := by omega
    have hpow : p ^ 2 ∣ Nat.card Model := by
      have hsub : Nat.card (P : Subgroup Model) ∣ Nat.card Model :=
        Subgroup.card_subgroup_dvd_card (P : Subgroup Model)
      rw [hn] at hsub
      exact (Nat.pow_dvd_pow p hn2).trans hsub
    have hpdiv : p ∣ Nat.card Model :=
      (dvd_pow_self p (by decide : 2 ≠ 0)).trans hpow
    rw [model_card_factorization] at hpow hpdiv
    have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 19 := by
      have hp : p.Prime := Fact.out
      rcases hp.dvd_mul.mp hpdiv with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · left
              exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
                (hp.dvd_of_dvd_pow h)
            · right; left
              exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
                (hp.dvd_of_dvd_pow h)
          · right; right; left
            exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
        · right; right; right; left
          exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
      · right; right; right; right
        exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact (hp2 rfl).elim
    · exact (hp3 rfl).elim
    · norm_num at hpow
    · norm_num at hpow
    · norm_num at hpow

private theorem odd_prime_not_dvd_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ∣ Nat.card f.ker := by
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (fun P => sylow_cyclic_of_odd_prime_ne_three hp2 hp3 P)

/-- Only two and three can divide a finite perfect central kernel over the
actual J₃ model. This does not yet exclude a two-primary kernel. -/
public theorem kernel_prime_eq_two_or_three
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card f.ker) : p = 2 ∨ p = 3 := by
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  · right
    by_contra hp3
    exact odd_prime_not_dvd_kernel f hf hk hp2 hp3 hp

/-- Excluding two-divisibility and nine-divisibility is sufficient for the
full upper bound. All other primes are excluded by the checked model order
and cyclic-Sylow transfer. The two local bounds remain explicit. -/
public theorem kernel_card_dvd_three_of_primary_bounds
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E)
    (h2 : ¬ 2 ∣ Nat.card f.ker) (h9 : ¬ 9 ∣ Nat.card f.ker) :
    Nat.card f.ker ∣ 3 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hkpow
  by_cases hk0 : k = 0
  · simp [hk0]
  let : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ Nat.card f.ker :=
    (show p ∣ p ^ k by simpa using pow_dvd_pow p (by omega : 1 ≤ k)).trans hkpow
  rcases kernel_prime_eq_two_or_three f hf hk hpd with h | h
  · exact (h2 (h ▸ hpd)).elim
  · subst p
    have hk1 : k ≤ 1 := by
      by_contra! h
      exact h9 ((pow_dvd_pow 3 h).trans hkpow)
    simpa using pow_dvd_pow 3 hk1

/-- In a finite perfect central cover of the concrete J₃ model, a nontrivial
odd-prime-power kernel can only have prime `3`.

The statement uses the literal quotient map to `Model` and therefore applies
before transporting along the source theorem's model equivalence. -/
public theorem odd_prime_power_kernel_prime_eq_three
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hkp : IsPGroup p f.ker)
    (hne : f.ker ≠ ⊥) : p = 3 := by
  by_contra hp3
  have hnot := odd_prime_not_dvd_kernel f hf hk hp2 hp3
  rcases hkp.card_eq_or_dvd with hcard | hdiv
  · exact hne (Subgroup.card_eq_one.mp hcard)
  · exact hnot hdiv

/-- A nontrivial odd-primary central kernel over J₃ is a 3-group. -/
public theorem kernel_eq_bot_of_odd_prime_ne_three
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hkp : IsPGroup p f.ker) :
    f.ker = ⊥ := by
  rcases hkp.card_eq_or_dvd with hcard | hdiv
  · exact Subgroup.card_eq_one.mp hcard
  · exact (odd_prime_not_dvd_kernel f hf hk hp2 hp3 hdiv).elim

/-- The source-domain form for an actual central quotient equivalence.
The explicit `[IsQuasisimple Model]` hypothesis is the source interface; it
is not used to hide a model replacement or a presentation identification. -/
public theorem source_center_eq_bot_of_odd_prime_ne_three
    [IsQuasisimple Model]
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hZ : IsPGroup p (center E)) : center E = ⊥ := by
  let f : E →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp
    (QuotientGroup.mk'_surjective (center E))
  have hker : f.ker = center E := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk']
  have hbot : f.ker = ⊥ := kernel_eq_bot_of_odd_prime_ne_three f hf
    (hker.le) hp2 hp3 (hker.symm ▸ hZ)
  exact hker.symm ▸ hbot

/-- The source-domain prime-forcing form used by the A.2.19 assembly: a
nontrivial odd-prime-power center in a quasisimple source cover has prime `3`.
The cover owner still supplies the independent nontriviality and the source
equivalence; no universal-cover or multiplier conclusion is inferred here. -/
public theorem source_center_prime_eq_three
    [IsQuasisimple Model]
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* Model) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hZ : IsPGroup p (center E))
    (hZne : center E ≠ ⊥) : p = 3 := by
  let f : E →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp
    (QuotientGroup.mk'_surjective (center E))
  have hker : f.ker = center E := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
      QuotientGroup.ker_mk']
  exact odd_prime_power_kernel_prime_eq_three f hf hker.le hp2
    (hker.symm ▸ hZ) (hker.symm ▸ hZne)

/-- The exact chosen-cover assembly after the two remaining primary bounds
and an actual perfect central triple cover have been supplied. In particular,
an odd-prime restriction alone is not treated as the full upper bound. -/
public theorem source_kernel_equiv_three_of_primary_bounds_and_triple_cover
    [IsQuasisimple Model]
    {U E : Type*} [Group U] [Finite U] [IsQuasisimple U]
    [Group E] [Finite E]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, _, 0} f)
    (h2 : ¬ 2 ∣ Nat.card (universalProjection Model).ker)
    (h9 : ¬ 9 ∣ Nat.card (universalProjection Model).ker)
    (c : Cover E Model) (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 3)) := by
  have hd := kernel_card_dvd_three_of_primary_bounds (universalProjection Model)
    (universalProjection_surjective Model) (universalProjection_ker_le_center Model) h2 h9
  exact Multiplier.source_kernel_equiv_three_of_bound_and_triple_cover f hf
    (Nat.le_of_dvd (by decide) hd) c hc

/-- The marked local three-extension bound and the independent exclusion of
two give the full kernel upper bound. The local bound is transferred through
the actual subgroup inclusion, and all other primes are already excluded. -/
public theorem kernel_card_le_three_of_local_bound_and_two_exclusion
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E)
    (hlocal : Multiplier.LocalThreeKernelBound.{u})
    (h2 : ¬ 2 ∣ Nat.card f.ker) : Nat.card f.ker ≤ 3 := by
  have h9 := Multiplier.kernel_not_nine_dvd_of_local_bound hlocal f hf hk
  exact Nat.le_of_dvd (by decide)
    (kernel_card_dvd_three_of_primary_bounds f hf hk h2 h9)

end Sporadic.Janko3
