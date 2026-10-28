module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes.Arithmetic
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes.ModelCentralizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes.Dickson
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Tori
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels

/-!
# Missing centralizer primes in prime-square PSL₂

For every four-group A in a Sylow two-subgroup T and every maximal
subgroup M containing T, select a nonidentity z in A and an odd torus
prime missing from C_M(z). Dickson reduces M to dihedral, S₄ or PGL₂(p).
A reflection handles the dihedral case; S₄ centralizers have order four
or eight. In PGL₂(p), an inner actor involution and a prime from the
opposite torus half give the separation. The argument includes p = 5.

Applying the previously proved torus construction then gives an escaping
local model through A, with the literal intersection with T Sylow in it.
This supplies exactly the numerical input of
`InnerPlacement.concreteLocalGeometryAt_of_missing_centralizer_primes`.

Source: Aschbacher--Smith A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209--210 and 214; Huppert II.8.27 and the cited Asc82a, Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

private theorem actor_centralizer_four_dvd {G : Type*} [Group G] [Finite G]
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M)
    (z : G) (hz : z ∈ A) :
    4 ∣ Nat.card ((centralizer ({z} : Set G)).subgroupOf M) := by
  let : IsKleinFour A := hA
  have hle : A.subgroupOf M ≤ (centralizer ({z} : Set G)).subgroupOf M := by
    intro x hx
    change (x : G) ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨x, hx⟩ : A) ⟨z, hz⟩)
  have hd := card_dvd_of_le hle
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv, hA.card_four] at hd

private theorem not_dvd_four_or_eight {r c : ℕ} (hr : r.Prime) (ho : Odd r)
    (h4 : 4 ∣ c) (hc : 0 < c) (hle : c ≤ 8) : ¬ r ∣ c := by
  obtain ⟨a, ha⟩ := h4
  have hcases : c = 4 ∨ c = 8 := by omega
  have hr2 : ¬ r ∣ 2 := by
    intro h
    have heq : r = 2 := le_antisymm (Nat.le_of_dvd (by decide) h) hr.two_le
    subst r
    exact ho.not_two_dvd_nat (dvd_refl 2)
  intro h
  rcases hcases with rfl | rfl
  · exact hr2 (hr.dvd_of_dvd_pow (n := 2) h)
  · exact hr2 (hr.dvd_of_dvd_pow (n := 3) h)

/-- The elementary dihedral calculation supplies separation through every
four-group actor, by choosing a reflection outside the cyclic rotations. -/
theorem separation_dihedral
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hodd : Odd p) (hp5 : 5 ≤ p)
    (A M : Subgroup (PSL2 F)) (hA : IsKleinFour A) (hAM : A ≤ M)
    {k : ℕ} (hk : 0 < k) (eM : M ≃* DihedralGroup (2 * k)) :
    ∃ (z : PSL2 F) (r : ℕ), z ∈ A ∧ z ≠ 1 ∧ r.Prime ∧ Odd r ∧
      r ∣ (p ^ 2 - 1) / 2 ∧
      ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M) := by
  obtain ⟨z, hzA, hz1, hc⟩ :=
    CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups.dihedral_actor_centralizer
      A M hA hAM hk eM
  obtain ⟨r, hr, ho, hd⟩ := torus_prime hodd hp5
  exact ⟨z, r, hzA, hz1, hr, ho, hd,
    not_dvd_four_or_eight hr ho (actor_centralizer_four_dvd A M hA hAM z hzA)
      Nat.card_pos (by omega)⟩

/-- The involution centralizers in S₄ have order four or eight; hence the
odd prime of the prime-square torus is absent. -/
theorem separation_symmetric_four
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hodd : Odd p) (hp5 : 5 ≤ p)
    (A M : Subgroup (PSL2 F)) (hA : IsKleinFour A) (hAM : A ≤ M)
    (eM : M ≃* Equiv.Perm (Fin 4)) :
    ∃ (z : PSL2 F) (r : ℕ), z ∈ A ∧ z ≠ 1 ∧ r.Prime ∧ Odd r ∧
      r ∣ (p ^ 2 - 1) / 2 ∧
      ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M) := by
  let : IsKleinFour A := hA
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA.card_four]; decide)
  obtain ⟨z, hzA, hz1⟩ := A.exists_ne_one_of_nontrivial
  let a : M := ⟨z, hAM hzA⟩
  have he1 : eM a ≠ 1 := by
    intro h
    apply hz1
    exact congrArg Subtype.val (eM.injective (h.trans eM.map_one.symm))
  have he2 : eM a ^ 2 = 1 := by
    rw [← map_pow]
    have ha2 : a ^ 2 = 1 := by
      apply Subtype.ext
      change z ^ 2 = 1
      rw [pow_two]
      exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzA⟩ : A))
    rw [ha2, map_one]
  have hc : Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M) ≤ 8 := by
    rw [relative_centralizer_card_equiv M eM a]
    exact CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups.symmetric_four_involution_centralizer
      (eM a) he1 he2
  obtain ⟨r, hr, ho, hd⟩ := torus_prime hodd hp5
  exact ⟨z, r, hzA, hz1, hr, ho, hd,
    not_dvd_four_or_eight hr ho (actor_centralizer_four_dvd A M hA hAM z hzA)
      Nat.card_pos hc⟩

/-- A four-group in a PGL₂(p) overgroup supplies an inner involution.
The odd prime from the opposite torus half misses its literal centralizer. -/
theorem separation_pgl
    {F K : Type*} [Field F] [Finite F] [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hp5 : 5 ≤ p) (hK : Nat.card K = p)
    (A M : Subgroup (PSL2 F)) (hA : IsKleinFour A) (hAM : A ≤ M)
    (eM : M ≃* PGL2 K) :
    ∃ (z : PSL2 F) (r : ℕ), z ∈ A ∧ z ≠ 1 ∧ r.Prime ∧ Odd r ∧
      r ∣ (p ^ 2 - 1) / 2 ∧
      ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M) := by
  obtain ⟨z, hzA, hz1, hc⟩ := pgl_actor_centralizer_divisibility hp hodd hK A M hA hAM eM
  obtain ⟨r, hr, ho, hd, hn⟩ := opposite_half_prime hodd hp5 hc
  exact ⟨z, r, hzA, hz1, hr, ho, hd, hn⟩

/-- Numerical separation for all proper Sylow overgroups of PSL₂(p²),
including p = 5 and the genuine PGL₂(p) subfield alternative. -/
theorem missing_centralizer_prime
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PSL2 F)) (A M : Subgroup (PSL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup (PSL2 F)))
    (hM : IsCoatom M) (hTM : (T : Subgroup (PSL2 F)) ≤ M) :
    ∃ (z : PSL2 F) (r : ℕ), z ∈ A ∧ z ≠ 1 ∧ r.Prime ∧ Odd r ∧
      r ∣ (p ^ 2 - 1) / 2 ∧
      ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M) := by
  let : Fact p.Prime := ⟨hp⟩
  have hAM := hAT.trans hTM
  rcases square_sylow_overgroup_cases hodd hF T M hTM hM.1 with hD | hS | hP
  · obtain ⟨n, _hn, hc, ⟨eM⟩⟩ := hD
    have h4 : 4 ∣ 2 * n := by
      rw [← hc, ← hA.card_four]
      exact card_dvd_of_le hAM
    obtain ⟨k, hk⟩ := h4
    have hn : n = 2 * k := by omega
    have hpos : 0 < k := by
      have hcpos : 0 < Nat.card M := Nat.card_pos
      omega
    subst n
    exact separation_dihedral hodd hp5 A M hA hAM hpos eM
  · exact separation_symmetric_four hodd hp5 A M hA hAM hS.some
  · have hK : Nat.card (GaloisField p 1) = p := by
      simpa using GaloisField.card p 1 (by decide)
    exact separation_pgl hp hodd hp5 hK A M hA hAM hP.1.some

/-- Actual application to the torus construction: the escaping LocalModel
contains A and retains the literal Sylow intersection required by E0. -/
theorem escaping_local_model
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PSL2 F)) (A M : Subgroup (PSL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup (PSL2 F)))
    (hM : IsCoatom M) (hTM : (T : Subgroup (PSL2 F)) ≤ M) :
    ∃ H : Subgroup (PSL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PSL2 F)).subgroupOf H) ∧
      CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨z, r, hzA, hz1, hr, ho, hd, hn⟩ := missing_centralizer_prime hp hodd hp5 hF T A M hA hAT hM hTM
  exact CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.local_witness_of_missing_centralizer_prime
    hp hodd hF T A M hA hAT z hzA hz1 hr ho hd hn
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes
