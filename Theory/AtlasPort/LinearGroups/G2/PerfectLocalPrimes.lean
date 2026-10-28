module
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Odd primes in perfect subgroups of binary G₂ parabolics

A perfect subgroup lies in the parabolic's solvable residual. Each residual
has a two-group kernel and an SL₂ quotient. Transfer of odd-prime rank
through that kernel and the SL₂ order formula show that every odd prime
of the perfect subgroup divides q² − 1.

Source: Aschbacher--Smith A.3.12, printed pp.47--48; the local inspection
in 4.3.16, printed p.618. The actual root parabolics and quotient maps
come from the attributed ATLAS port.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.PerfectSubgroups

universe u

/-- An odd prime in a perfect subgroup of either actual parabolic divides the
quadratic torus factor. No full-Sylow containment is needed. -/
theorem prime_dvd_quadratic_of_perfect_local
    {F : Type u} [Field F] [Finite F] [CharP F 2]
    (hq : 2<Nat.card F) {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (j : B →* Atlas.G2.Model F) (hj : Function.Injective j)
    (hl : j.range ≤ Atlas.G2.LieParabolicSetup.parabolic₁ ∨
      j.range ≤ Atlas.G2.LieParabolicSetup.parabolic₂)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p∣Nat.card B) : p ∣ Nat.card F^2-1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : 1≤primeRank p B := by
    by_contra hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega) hd
  have quotient_prime {C : Type u} [Group C] [Finite C]
      (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (hBC : primeRank p B ≤ primeRank p C) : p ∣ Nat.card F^2-1 := by
    have hc : p∣Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      by_contra hh
      have hz : primeRank p C=0 := by
        rw [←primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,primeRank_congr p e]
        exact PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      omega
    rw [Atlas.card_sl_two] at hc
    have hpF : ¬p∣Nat.card F := by
      let := Fintype.ofFinite F
      obtain ⟨d,_,hF⟩ := FiniteField.card F 2
      rw [Nat.card_eq_fintype_card,hF]
      intro hh
      have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hh)
      subst p
      exact ho.not_two_dvd_nat (dvd_refl 2)
    exact (hp.dvd_mul.mp hc).resolve_left hpF
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hl with hl | hl
  · have hl' : j.range ≤ Atlas.G2.LieParabolicSetup.local₁ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hl
    let k := j.codRestrict _ (fun b => hl' ⟨b,rfl⟩)
    apply quotient_prime ((Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL (F:=F)).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F)).symm)
    exact Theory.GroupTheory.primeRank_le_of_injective p k
      (fun x y he => hj (congrArg Subtype.val he))
  · have hl' : j.range ≤ Atlas.G2.LieParabolicSetup.local₂ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hl
    let k := j.codRestrict _ (fun b => hl' ⟨b,rfl⟩)
    apply quotient_prime ((Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL (F:=F)).trans
      (Atlas.G2.LieParabolicSetup.longSLEquivPSL (F:=F)).symm)
    exact Theory.GroupTheory.primeRank_le_of_injective p k
      (fun x y he => hj (congrArg Subtype.val he))

end Atlas.G2.PerfectSubgroups
