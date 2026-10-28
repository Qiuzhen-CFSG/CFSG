module

public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.Representation.NonsplitFourCyclicity
public import Theory.GroupTheory.PerfectCentralCover

/-!
# The fourth-cyclotomic primes in even symplectic four-space

If an odd prime does not divide q²−1, the actual symplectic group order
shows that a Sylow subgroup has order dividing q²+1. The faithful matrix
embedding into GL₄(F) then makes it cyclic by `NonsplitFourCyclicity`,
whose proof uses irreducible centralizers and Singer normalizer actions.
Cyclic Sylow transfer excludes this prime from every finite perfect
central kernel. The order formula is used only to apply that structural
theorem; it is not itself a multiplier calculation.

Source: Aschbacher–Smith I.1.2–I.1.3, printed p.407, and the
Huppert–Blackburn XI.3.10(a) argument cited by `NonsplitFourCyclicity`.
-/

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Away from q²−1, an odd Sylow subgroup of the actual Sp₄(F) is cyclic. -/
public theorem sylow_isCyclic_of_not_dvd_sq_sub_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : ¬ p ∣ (Nat.card F)^2 - 1) (P : Sylow p (Sp F)) :
    IsCyclic P := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hp : p.Prime := Fact.out
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hn' : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hn']
    intro h
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) ((Nat.card F)^4 * ((Nat.card F)^2 - 1)^2) := by
    rw [hm]
    apply Nat.Coprime.pow_left
    apply hp.coprime_iff_not_dvd.mpr
    exact hp.not_dvd_mul (fun h => hpq (hp.dvd_of_dvd_pow h))
      (fun h => hd (hp.dvd_of_dvd_pow h))
  have hcard : Nat.card P ∣ (Nat.card F)^2 + 1 := by
    apply hcop.dvd_of_dvd_mul_left
    have h := (P : Subgroup (Sp F)).card_subgroup_dvd_card
    rw [card_sp] at h
    have hpos : 1 ≤ (Nat.card F)^2 := Nat.one_le_pow _ _ Nat.card_pos
    have he : (Nat.card F)^4 - 1 = ((Nat.card F)^2 - 1) * ((Nat.card F)^2 + 1) := by
      have h1 := Nat.sub_add_cancel hpos
      have h2 := Nat.sub_add_cancel (show 1 ≤ (Nat.card F)^4 by
        exact Nat.one_le_pow _ _ Nat.card_pos)
      nlinarith [sq_nonneg ((Nat.card F)^2 - 1)]
    rw [he] at h
    convert h using 1; ring
  let μ : Sp F →* Matrix (Fin 4) (Fin 4) F :=
    (Matrix.reindexRingEquiv F (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).toMonoidHom.comp
      (Matrix.symplecticGroup (Fin 2) F).subtype
  have hμ : Function.Injective μ :=
    (Matrix.reindexRingEquiv F finSumFinEquiv).injective.comp Subtype.val_injective
  let ρ : Sp F →* GL (Fin 4) F := μ.toHomUnits
  have hρ : Function.Injective ρ := fun a b h => hμ (congrArg Units.val h)
  let U := (P : Subgroup (Sp F)).map ρ
  have hU : Nat.card U ∣ Fintype.card F ^ 2 + 1 := by
    rw [Subgroup.card_map_of_injective hρ]
    simpa only [Nat.card_eq_fintype_card] using hcard
  let : IsCyclic U := Representation.isCyclic_of_card_dvd_sq_add_one U hU
  exact isCyclic_of_injective (ρ.subgroupMap (P : Subgroup (Sp F)))
    (fun a b h => Subtype.ext (hρ (congrArg Subtype.val h)))

/-- Cyclic Sylow transfer excludes the primes supported on q²+1. -/
public theorem not_dvd_card_kernel_of_not_dvd_sq_sub_one
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : ¬ p ∣ (Nat.card F)^2 - 1)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ p ∣ Nat.card f.ker :=
  PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_not_dvd_sq_sub_one hp2 hd)

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
