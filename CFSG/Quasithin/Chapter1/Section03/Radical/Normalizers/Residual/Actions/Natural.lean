module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Actions.Transfer

/-!
# Residual actions in the natural radical case

In A.3.6(3), the Fitting subgroup is the actual natural module for SL₂(p).
Its only Fitting prime is p. Matrix transitivity proves irreducibility,
and the quotient and Frattini equivalences transfer it to Ξ_p(L).
The residual Frattini factorization and two-perfectness then prove both
residual action conclusions for every odd Fitting prime.

The input is the genuine natural-module structural witness, including its
field, quotient isomorphism and conjugation identity. No residual action
or containment assertion is assumed. The nilpotent alternative is separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6(3), printed pp.43–45, and proof of 1.3.8, printed pp.512–513.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open Section02 RadicalActions

private theorem natural_omega_irreducible
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hnat : A36Natural K) (hd : p ∣ Nat.card (fittingSubgroup K)) :
    ∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ k : K, ∀ a ∈ A, omegaFrattiniAction p K k a ∈ A) → A = ⊥ ∨ A = ⊤ := by
  obtain ⟨hfit, r, hr, hr3, ha⟩ := hnat
  obtain ⟨helem, hc⟩ := RadicalStructure.natural_elementary ha
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ r ^ 2 by
      simpa only [← hfit, hc] using hd))
  subst r
  have hGF : generalizedFitting K = pCore p K := hfit.trans
    (RadicalStructure.fitting_eq_core (by rw [← hfit]; exact IsPGroup.of_card hc))
  let : IsElementaryAbelian p (pCore p K) := hGF ▸ helem
  have hW : omegaCore p K = generalizedFitting K := by
    unfold omegaCore
    rw [RadicalStructure.omega_top
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (pCore p K))),
      ← MonoidHom.range_eq_map, range_subtype]
    exact hGF.symm
  have hw : LocalModels.NaturalSL2Action K (omegaCore p K) p := by
    simpa only [hW] using ha
  intro A hA
  let f := QuotientGroup.mk' (frattini (omegaCore p K))
  have hi := natural_irreducible hw (A.comap f) (by
    intro g x hx
    change f (omegaCoreAction p K g x) ∈ A
    simpa only [omegaFrattiniAction, MonoidHom.comp_apply, f, quotientAut_apply_mk]
      using hA g (f x) hx)
  have hf := QuotientGroup.mk'_surjective (frattini (omegaCore p K))
  rcases hi with hb | ht
  · left
    have hm := congrArg (map f) hb
    simpa only [map_comap_eq_self_of_surjective (f := f) hf A, Subgroup.map_bot] using hm
  · right
    have hm := congrArg (map f) ht
    simpa only [map_comap_eq_self_of_surjective (f := f) hf A,
      map_top_of_surjective f hf] using hm

variable {G : Type*} [Group G] [Finite G]

/-- All relevant residual actions in the genuine natural-module alternative.
Both prime divisors coincide because the Fitting subgroup has order p². -/
theorem XiP_Y_actions_of_natural
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hnat : A36Natural (XiQuotient L))
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hdq : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L ∧
    ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  have hqp : q = p := by
    obtain ⟨hfit, r, hr, _, ha⟩ := hnat
    obtain ⟨_, hc⟩ := RadicalStructure.natural_elementary ha
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ r ^ 2 by
        simpa only [← hfit, hc] using hdp))
    have hqr : q = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow (show q ∣ r ^ 2 by
        simpa only [← hfit, hc] using hdq))
    exact hqr.trans hpr.symm
  subst q
  apply XiP_Y_actions_of_L_irreducible p L T hL hT
  · exact (RadicalStructure.core_omega (Or.inl hnat) hdp).2.of_mulEquiv
      (xiPQuotientEquivOmega hp L).symm
  · exact L_irreducible_of_omega_irreducible p hp L (natural_omega_irreducible hnat hdp)

end CFSG.Quasithin.Chapter1.RadicalNormalizers
