module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Omega

/-!
# Natural coordinates on the radical omega–Frattini quotient

In A.3.6(3), a prime dividing the Fitting subgroup is the defining prime.
The p-core equals F*(K), is elementary abelian, and hence equals its first
omega subgroup and has trivial Frattini subgroup. These equalities transport
the supplied natural-module coordinates to the exact quotient used by the
radical action. The matrix map is the supplied quotient isomorphism composed
with the quotient projection; its action formula is the original conjugation
identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(3),
pp.43–45, and the radical construction preceding 1.3.3 on p.509.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

/-- Natural-module coordinates on the actual omega–Frattini quotient, with a
surjective matrix quotient map and the conjugation identity. -/
theorem natural_coordinates (h : A36Natural K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      ∃ (v : (omegaCore p K ⧸ frattini (omegaCore p K)) ≃*
          Multiplicative (Fin 2 → F)) (q : K →* SL(2,F)),
        Function.Surjective q ∧ ∀ g x,
          v (omegaFrattiniAction p K g x) = Matrix.SL2.naturalAction F (q g) (v x) := by
  obtain ⟨hFit, r, hr, _, ha⟩ := h
  have hec := RadicalStructure.natural_elementary ha
  have hd : p ∣ r ^ 2 := by simpa only [← hFit, hec.2] using hp
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
  subst r
  have hfit : fittingSubgroup K = pCore p K := RadicalStructure.fitting_eq_core (by
    rw [← hFit]
    exact IsPGroup.of_card hec.2)
  have hGF : generalizedFitting K = pCore p K := hFit.trans hfit
  have hel : IsElementaryAbelian p (pCore p K) := hGF ▸ hec.1
  let := hel
  have hω : omegaCore p K = generalizedFitting K := by
    unfold omegaCore
    rw [RadicalStructure.omega_top (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (pCore p K)))]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hGF.symm
  have heW : IsElementaryAbelian p (omegaCore p K) := hω.symm ▸ hec.1
  let := heW
  let : Fact (IsPGroup p (omegaCore p K)) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  have hfr : frattini (omegaCore p K) = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := p)
  let mk := QuotientGroup.mk' (frattini (omegaCore p K))
  let eQ : omegaCore p K ≃* (omegaCore p K ⧸ frattini (omegaCore p K)) :=
    MulEquiv.ofBijective mk ⟨(MonoidHom.ker_eq_bot_iff mk).mp (by
      change (QuotientGroup.mk' _).ker = ⊥
      rw [QuotientGroup.ker_mk', hfr]), QuotientGroup.mk'_surjective _⟩
  obtain ⟨F, hField, hFin, hcard, v, ρ, hact⟩ := ha
  let eN : omegaCore p K ≃* generalizedFitting K := MulEquiv.subgroupCongr hω
  let e := (eQ.symm.trans eN).trans v
  let q : K →* SL(2,F) := ρ.toMonoidHom.comp (QuotientGroup.mk' (generalizedFitting K))
  refine ⟨F, hField, hFin, hcard, e, q,
    ρ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  intro g x
  obtain ⟨a, rfl⟩ := eQ.surjective x
  have hmk (a : omegaCore p K) : e (eQ a) = v (eN a) := by
    simp only [e, MulEquiv.trans_apply, eQ.symm_apply_apply]
  have heq : omegaFrattiniAction p K g (eQ a) = eQ (omegaCoreAction p K g a) := by
    change omegaFrattiniAction p K g (QuotientGroup.mk' _ a) =
      QuotientGroup.mk' _ (omegaCoreAction p K g a)
    simp only [omegaFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
  rw [heq, hmk, hmk]
  exact hact g (eN a)

end CFSG.Quasithin.Chapter1.RadicalActions
