module

public import Theory.GroupTheory.SolvableRadical.PrimaryResidualImage
public import Theory.GroupTheory.ReducedNormal.Basic

/-!
# Detecting a radical action by its primary residuals

If every odd-primary residual of a finite group is killed by an action,
the action image is a two-group: the residual at an odd prime has index
coprime to that prime. Thus a normal solvable subgroup whose odd-primary
residuals centralize a reduced binary subgroup centralizes it itself.
This gives the final assembly over all original Fitting primes in
Aschbacher--Smith 3.2.14, p.585.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Killing every odd-primary residual makes the actual action image a two-group. -/
theorem isTwoGroup_range_of_primeToResidual_le_ker (f : G →* H)
    (hkill : ∀ p : ℕ, p.Prime → Odd p → primeToResidual p G ≤ f.ker) :
    IsPGroup 2 f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
  rcases hprime.eq_two_or_odd' with he | ho
  · simpa only [he] using Nat.prime_two.mem_primeFactors_self
  · let : Fact p.Prime := ⟨hprime⟩
    have hc : Nat.Coprime p (Nat.card f.range) := by
      rw [← index_ker]
      exact (primeToResidual_index_coprime p).coprime_dvd_right
        (index_dvd_of_le (hkill p hprime ho))
    have hd := Nat.dvd_gcd (dvd_refl p) hdiv
    rw [hc] at hd
    exact (hprime.not_dvd_one hd).elim

/-- A normal subgroup is detected on a reduced binary group by its
actual odd-primary residuals. -/
theorem normal_centralizes_reduced_of_primary_residuals [Finite H]
    (N : Subgroup H) [N.Normal] (V : Subgroup H) (hV : IsPReduced 2 V)
    (hkill : ∀ p : ℕ, p.Prime → Odd p →
      (primeToResidual p N).map N.subtype ≤ centralizer (V : Set H)) :
    N ≤ centralizer (V : Set H) := by
  let := hV.normal
  let C := centralizer (V : Set H)
  let q := QuotientGroup.mk' C
  let f := q.comp N.subtype
  have hp : IsPGroup 2 f.range := isTwoGroup_range_of_primeToResidual_le_ker f (by
    intro p hprime ho x hx
    exact (QuotientGroup.eq_one_iff (x : H)).mpr
      (hkill p hprime ho (mem_map_of_mem N.subtype hx)))
  have hr : f.range = N.map q := by rw [MonoidHom.range_comp,range_subtype]
  have hN : N.map q ≤ pCore 2 (H ⧸ C) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective C),hr ▸ hp⟩
  have hz : N.map q = ⊥ := bot_unique (hN.trans_eq hV.quotient_pCore_eq_bot)
  simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz

end Theory.GroupTheory
