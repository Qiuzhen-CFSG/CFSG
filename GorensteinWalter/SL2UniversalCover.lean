module

public import GorensteinWalter.SL2ProjectiveCover
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.CentralDihedralSylow

/-!
# Universal PSL₂ covers over prime fields and reduction for extension fields

The actual SL₂ projection is a finite quasisimple covering. Its odd-field
kernel is multiplicatively equivalent to C₂. Over a prime field of order
larger than three, all odd Sylow subgroups of PSL₂ are cyclic. Transfer
eliminates the odd primes from the universal kernel, while the dihedral
Sylow theorem bounds its two-part by two. The canonical double cover then
attains that bound and is universal, with compatible unique lifts.

For extension fields the same proof leaves exactly the defining-prime
exclusion explicit. In even characteristic that exclusion makes the identity
cover universal. These conditional statements do not assert the missing
exclusion, and in particular do not incorrectly discard the exceptional
three-part at q = 9 or the two-part at q = 4.

Source: Aschbacher–Smith, I.1.3(1),(3) and I.1.4(1), printed pp.407–408.
The two-primary input is the central dihedral Sylow calculation used in
Alperin–Brauer–Gorenstein, Chapter II, §3, Proposition 2.
-/

public section
noncomputable section

open Theory.GroupTheory
open scoped MatrixGroups
namespace GorensteinWalter.PSL2Cover
universe u w
variable (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]

instance sl_quasisimple : IsQuasisimple SL(2, F) where
  toIsPerfect := sl2_isPerfect_of_card_gt_three F Fact.out
  simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by have := Fact.out (p := 3 < Nat.card F); omega)

instance psl_quasisimple : IsQuasisimple PSL(2, F) :=
  IsQuasisimple.of_surjective (sl2ProjectiveProjection F) (sl2ProjectiveProjection_surjective F)

@[expose] noncomputable def cover : Covering SL(2, F) PSL(2, F) where
  toMonoidHom := sl2ProjectiveProjection F
  surjective := sl2ProjectiveProjection_surjective F

noncomputable def kernelEquivTwo (ho : Odd (Nat.card F)) :
    (cover F).toMonoidHom.ker ≃* Multiplicative (ZMod 2) := by
  have hc : Nat.card (cover F).toMonoidHom.ker = 2 := sl2ProjectiveProjection_ker_card F ho
  let : IsCyclic (cover F).toMonoidHom.ker := isCyclic_of_prime_card hc
  exact mulEquivOfCyclicCardEq (by simpa using hc)

theorem kernel_le_two_of_isPGroup {E : Type*} [Group E] [Finite E]
    [IsQuasisimple E] (g : Covering E PSL(2, F))
    (ho : Odd (Nat.card F)) (hk : IsPGroup 2 g.toMonoidHom.ker) :
    Nat.card g.toMonoidHom.ker ≤ 2 := by
  let S : Sylow 2 E := Classical.choice inferInstance
  obtain ⟨n, hn, ⟨e⟩⟩ := psl2_dihedral_sylow_of_odd_card F ho
    (Sylow.mapSurjective g.surjective S)
  let : NeZero n := ⟨hn.ne'⟩
  simpa only [Group.IsPerfect.commutator_eq_top, inf_top_eq] using
    CentralExtension.card_ker_inf_commutator_le_two_of_dihedral_sylow
      g.toMonoidHom g.surjective g.ker_le_center hk S e

theorem isUniversal_of_kernel_isPGroup (ho : Odd (Nat.card F))
    (hk : IsPGroup 2 (PerfectCentralCovering.universalProjection PSL(2, F)).ker) :
    Covering.IsUniversal.{u, u, w} (cover F) := by
  apply Covering.isUniversal_of_kernel_card_le
  rw [show Nat.card (cover F).toMonoidHom.ker = 2 from sl2ProjectiveProjection_ker_card F ho]
  exact kernel_le_two_of_isPGroup F (PerfectCentralCovering.universalQuasisimpleCover PSL(2, F)) ho hk

omit [Fact (3 < Nat.card F)] in
private theorem odd_sylow_cyclic_card_five (hF : Nat.card F = 5)
    (r : ℕ) [Fact r.Prime] (hr : r ≠ 2) (R : Sylow r PSL(2, F)) : IsCyclic R := by
  have hG : Nat.card PSL(2, F) = 60 := by
    rw [psl2_card_formula F ⟨5, 1, by decide, by decide, by decide, by simpa using hF⟩, hF]
    norm_num
  obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
  have hd : r ^ n ∣ 60 := by simpa [hn, hG] using R.card_subgroup_dvd_card
  have hle : n ≤ 1 := by
    by_contra hle
    have hn2 : 2 ≤ n := by omega
    have hd2 : r ^ 2 ∣ 60 := (pow_dvd_pow r hn2).trans hd
    have hdr : r ∣ 60 := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hd2
    have hf : r = 2 ∨ r = 3 ∨ r = 5 := by
      have hd' : r ∣ 2 * 2 * 3 * 5 := by simpa using hdr
      rw [Nat.Prime.dvd_mul Fact.out, Nat.Prime.dvd_mul Fact.out,
        Nat.Prime.dvd_mul Fact.out] at hd'
      have h2 := Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two
      have h3 := Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_three
      have h5 := Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (by decide : Nat.Prime 5)
      tauto
    rcases hf with h | h | h <;> subst r <;> norm_num at *
  exact isCyclic_of_card_dvd_prime (p := r) (hn ▸ (by simpa using pow_dvd_pow r hle))

/-- Only the defining prime remains after cyclic-torus transfer. -/
theorem odd_prime_not_dvd_kernel {E : Type*} [Group E] [Finite E]
    [IsQuasisimple E] (g : Covering E PSL(2, F))
    (hF : 7 ≤ Nat.card F) (r : ℕ) [Fact r.Prime] (hr : r ≠ 2)
    (hrF : Nat.Coprime r (Nat.card F)) : ¬ r ∣ Nat.card g.toMonoidHom.ker := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  let : Fact (ringChar F).Prime := ⟨hp⟩
  exact (PerfectCentralCovering.ofCovering g).not_dvd_card_multiplier_of_isCyclic_sylow
    (psl2_sylow_isCyclic_of_coprime_field_card F
      (by simpa only [Nat.card_eq_fintype_card] using hn) hF r hr hrF)

/-- Over a prime field every odd Sylow subgroup of PSL₂ is cyclic. -/
theorem odd_sylow_cyclic_of_card_prime (hp : (Nat.card F).Prime)
    (r : ℕ) [Fact r.Prime] (hr : r ≠ 2) (R : Sylow r PSL(2, F)) : IsCyclic R := by
  have hcard : 3 < Nat.card F := Fact.out
  by_cases hf : Nat.card F = 5
  · exact odd_sylow_cyclic_card_five F hf r hr R
  have hseven : 7 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  by_cases he : r = Nat.card F
  · subst r
    obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
      (F := F) (f := 1) (by simp) R
    let : IsCyclic (Multiplicative F) := isCyclic_of_prime_card (p := Nat.card F) rfl
    exact e.isCyclic.mp inferInstance
  · let : Fact (Nat.card F).Prime := ⟨hp⟩
    exact psl2_sylow_isCyclic_of_coprime_field_card F
      (p := Nat.card F) (f := 1) (by simp) hseven r hr
      ((Fact.out : r.Prime).coprime_iff_not_dvd.mpr
        (by intro h; exact he ((Nat.prime_dvd_prime_iff_eq Fact.out hp).mp h))) R

/-- All kernels over the odd prime-field models are two-groups. -/
theorem kernel_isPGroup_of_card_prime {E : Type*} [Group E] [Finite E]
    [IsQuasisimple E] (g : Covering E PSL(2, F)) (hp : (Nat.card F).Prime) :
    IsPGroup 2 g.toMonoidHom.ker := by
  rw [isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)]
  intro r hr
  obtain ⟨hpr, hdr, _⟩ := Nat.mem_primeFactors.mp hr
  have he : r = 2 := by
    by_contra h
    let : Fact r.Prime := ⟨hpr⟩
    exact (PerfectCentralCovering.ofCovering g).not_dvd_card_multiplier_of_isCyclic_sylow
      (odd_sylow_cyclic_of_card_prime F hp r h) hdr
  norm_num [he]

/-- The actual SL₂ projection is universal over every field of prime order > 3. -/
theorem isUniversal_of_card_prime (hp : (Nat.card F).Prime) :
    Covering.IsUniversal.{u, u, w} (cover F) := by
  have ho : Odd (Nat.card F) := hp.odd_of_ne_two (by have := Fact.out (p := 3 < Nat.card F); omega)
  exact isUniversal_of_kernel_isPGroup F ho
    (kernel_isPGroup_of_card_prime F (PerfectCentralCovering.universalQuasisimpleCover PSL(2, F)) hp)

omit [Fact (3 < Nat.card F)] in
private theorem prime_coprime_card (r : ℕ) [Fact r.Prime] (h : r ≠ ringChar F) :
    Nat.Coprime r (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  rw [hcard]
  exact ((Nat.coprime_primes Fact.out hp).mpr h).pow_right _

/-- For general fields the only missing odd prime is the defining prime. -/
theorem kernel_isPGroup_of_defining_prime_not_dvd {E : Type*}
    [Group E] [Finite E] [IsQuasisimple E] (g : Covering E PSL(2, F))
    (hF : 7 ≤ Nat.card F) (hp : ¬ ringChar F ∣ Nat.card g.toMonoidHom.ker) :
    IsPGroup 2 g.toMonoidHom.ker := by
  rw [isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)]
  intro r hr
  obtain ⟨hpr, hdr, _⟩ := Nat.mem_primeFactors.mp hr
  have he : r = 2 := by
    by_contra h
    let : Fact r.Prime := ⟨hpr⟩
    by_cases he : r = ringChar F
    · exact hp (he ▸ hdr)
    · exact odd_prime_not_dvd_kernel F g hF r h (prime_coprime_card F r he) hdr
  norm_num [he]

/-- Conditional assembly for odd extension fields. The defining-prime
exclusion, which fails at q = 9, is the remaining source premise. -/
theorem isUniversal_of_defining_prime_not_dvd (ho : Odd (Nat.card F))
    (hF : 7 ≤ Nat.card F)
    (hp : ¬ ringChar F ∣ Nat.card (PerfectCentralCovering.universalProjection PSL(2, F)).ker) :
    Covering.IsUniversal.{u, u, w} (cover F) :=
  isUniversal_of_kernel_isPGroup F ho
    (kernel_isPGroup_of_defining_prime_not_dvd F
      (PerfectCentralCovering.universalQuasisimpleCover PSL(2, F)) hF hp)

/-- In characteristic two, defining-prime exclusion kills the whole kernel. -/
theorem kernel_card_one_of_even_of_defining_prime_not_dvd {E : Type*}
    [Group E] [Finite E] [IsQuasisimple E] (g : Covering E PSL(2, F))
    (hF : 7 ≤ Nat.card F) (heven : Even (Nat.card F))
    (hp : ¬ ringChar F ∣ Nat.card g.toMonoidHom.ker) : Nat.card g.toMonoidHom.ker = 1 := by
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr
    (by simpa only [← Nat.card_eq_fintype_card] using Nat.even_iff.mp heven)
  by_contra hn
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd hn
  let : Fact r.Prime := ⟨hr⟩
  by_cases he : r = 2
  · exact hp (by simpa only [hchar, he] using hd)
  · exact odd_prime_not_dvd_kernel F g hF r he
      (prime_coprime_card F r (by simpa only [hchar] using he)) hd

/-- Conditional assembly of the trivial multiplier for even q ≥ 8. -/
theorem identity_isUniversal_of_defining_prime_not_dvd
    (hF : 8 ≤ Nat.card F) (heven : Even (Nat.card F))
    (hp : ¬ ringChar F ∣ Nat.card (PerfectCentralCovering.universalProjection PSL(2, F)).ker) :
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering PSL(2, F) PSL(2, F)) := by
  apply Covering.isUniversal_of_kernel_card_le
  have hk := kernel_card_one_of_even_of_defining_prime_not_dvd F
    (PerfectCentralCovering.universalQuasisimpleCover PSL(2, F)) (by omega) heven hp
  change Nat.card (PerfectCentralCovering.universalProjection PSL(2, F)).ker = 1 at hk
  rw [hk]
  exact Nat.card_pos

end GorensteinWalter.PSL2Cover
