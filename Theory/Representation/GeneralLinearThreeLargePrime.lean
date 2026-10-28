module
public import Theory.Representation.RankThreePGroupIrreducible

/-!
# Large-prime subgroups of GL₃ in cross characteristic

A nonabelian odd p-subgroup of GL₃ is absolutely irreducible. Its degree
then divides its order, forcing p=3. Thus every cross-characteristic
p-subgroup with p>3 is abelian. This is the nonabelian exclusion used in
Aschbacher–Smith A.3.15(b), pp.50–51.
-/
public section

open Representation
namespace Representation

theorem generalLinear_three_large_prime_abelian
    {F : Type*} [Field F] [Finite F] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP F q] (hp : 3 < p) (hpq : p ≠ q)
    (P : Subgroup (GL (Fin 3) F)) (hP : IsPGroup p P) :
    IsMulCommutative P := by
  by_contra hn
  let : Group.IsNilpotent P := hP.isNilpotent
  let ρ := (generalLinearNatural (F := F) 3).comp P.subtype
  let : IsAbsolutelyIrreducible ρ :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hpq P hP hn
  have hd : 3 ∣ Nat.card P := by simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using lemma_2_3 ρ
  obtain ⟨a,ha⟩ := hP.exists_card_eq
  rw [ha] at hd
  have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hd
  have he := (Nat.dvd_prime (Fact.out : p.Prime)).mp h3p
  omega
end Representation
