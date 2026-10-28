module

public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# Initial reductions for noncentral Fitting C-components

A C-component with noncentral Fitting subgroup has no ordinary components:
any such component would fill it by minimality. Thus F* = F. Subnormal
prime-core transport gives trivial two-core, and the prime-core product
formula shows that F has odd order and that some odd core is noncentral.
No action-kernel equality or structural classification is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, opening of the noncentral branch, printed p.43.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem not_quasisimple_of_noncentral_fitting
    (hn : ¬ fittingSubgroup L ≤ center L) : ¬ IsQuasisimple L := by
  intro hq
  let := hq
  exact hn ((le_solvableRadical (fittingSubgroup L) inferInstance inferInstance).trans
    IsQuasisimple.solvableRadical_le_center)

theorem generalizedFitting_eq_fitting (hL : L.IsCComponent)
    (hn : ¬ fittingSubgroup L ≤ center L) :
    generalizedFitting L = fittingSubgroup L := by
  have hE : componentLayer L = ⊥ := by
    apply sSup_eq_bot.mpr
    intro J hJ
    have ht := hL.eq_top_of_isCComponent hJ.isCComponent
    let : IsQuasisimple (⊤ : Subgroup L) := ht ▸ hJ.2
    exact (not_quasisimple_of_noncentral_fitting hn
      (IsQuasisimple.of_mulEquiv topEquiv)).elim
  rw [generalizedFitting, hE, sup_bot_eq]

theorem twoCore_eq_bot (hL : L.IsCComponent) (hO : pCore 2 G = ⊥) :
    pCore 2 L = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 hL.subnormal, hO, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff L.subtype).mpr L.subtype_injective

theorem fitting_le_oddCore (hL : L.IsCComponent) (hO : pCore 2 G = ⊥) :
    fittingSubgroup L ≤ pPrimeCore 2 L :=
  fitting_le_pPrimeCore_of_pCore_eq_bot 2 (twoCore_eq_bot hL hO)

theorem fitting_odd_card (hL : L.IsCComponent) (hO : pCore 2 G = ⊥) :
    Odd (Nat.card (fittingSubgroup L)) := by
  have hc := (pPrimeCore_coprime_card (p := 2) (G := L)).of_dvd_right
    (Subgroup.card_dvd_of_le (fitting_le_oddCore hL hO))
  exact Nat.coprime_two_left.mp hc

theorem exists_noncentral_odd_core (hL : L.IsCComponent) (hO : pCore 2 G = ⊥)
    (hn : ¬ fittingSubgroup L ≤ center L) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ¬ pCore p L ≤ center L := by
  have hex : ∃ p : Nat.Primes, p.val ∣ Nat.card L ∧ ¬ pCore p.val L ≤ center L := by
    by_contra! hh
    apply hn
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    exact hh ⟨p.val.val, Nat.prime_of_mem_primeFactors p.val.property⟩
      (Nat.dvd_of_mem_primeFactors p.val.property)
  obtain ⟨p, _, hp⟩ := hex
  refine ⟨p.val, p.property, p.property.odd_of_ne_two ?_, hp⟩
  intro he
  apply hp
  rw [he, twoCore_eq_bot hL hO]
  exact bot_le
end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
