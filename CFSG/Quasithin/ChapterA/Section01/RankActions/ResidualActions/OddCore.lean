module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.Fitting.Centralizer
public import FeitThompson.FinalTheorem

/-!
# Detecting two-group actions on the odd core

The prime cores of a normal subgroup embed into the corresponding ambient
prime cores. The odd core is solvable by the odd-order theorem, hence its
generalized Fitting subgroup is its Fitting subgroup. Centralizing every
ambient odd prime core therefore centralizes this generalized Fitting
subgroup. The precise universal A.1.9 implication, left explicit here,
then gives centralization of the entire odd core.

Source: Aschbacher–Smith, A.1.9 and the first reduction in the proof of
A.1.26, printed pp.21 and 25–26. A.1.9 is owned by the Fitting development;
this module does not assert that input.
-/

public section

namespace CFSG.Quasithin.ChapterA.RankActions

open Subgroup Theory.GroupTheory

universe u

/-- The exact universal A.1.9 implication used by the residual-action proof. -/
@[expose] def PGroupFStarCentralizationInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (A Y : Subgroup G), IsPGroup p A → A ≤ normalizer (Y : Set G) →
      pCore p Y = ⊥ →
      A ≤ centralizer ((generalizedFitting Y).map Y.subtype : Set G) →
      A ≤ centralizer (Y : Set G)

private theorem generalizedFitting_eq_fitting_of_solvable
    (G : Type*) [Group G] [Group.IsSolvable G] :
    generalizedFitting G = fittingSubgroup G := by
  have hl : componentLayer G = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    rintro K ⟨_, hK⟩
    let : IsQuasisimple K := hK
    by_contra hn
    have hne : K ≠ ⊥ := fun he => hn he.le
    let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
    exact Group.IsPerfect.not_isSolvable K inferInstance
  simp only [generalizedFitting, hl, sup_bot_eq]

/-- Centralization of all odd prime cores detects a two-group's action on
O(G), using only the exact universal A.1.9 implication as an extra input. -/
theorem centralizes_oddCore_of_pCores_and_fStarInput
    (hfaith : PGroupFStarCentralizationInput.{u})
    {G : Type u} [Group G] [Finite G] (V : Subgroup G) (hV : IsPGroup 2 V)
    (hc : ∀ (p : ℕ) [Fact p.Prime], Odd p →
      V ≤ centralizer (pCore p G : Set G)) :
    V ≤ centralizer (pPrimeCore 2 G : Set G) := by
  let Y := pPrimeCore 2 G
  have hodd : Odd (Nat.card Y) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  let : Group.IsSolvable Y := odd_order_theorem Y hodd
  have hcore : pCore 2 Y = ⊥ := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
    have hcop := (Nat.coprime_two_left.mpr hodd).pow_left n
    rw [← hn] at hcop
    apply Subgroup.card_eq_one.mp
    exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (card_subgroup_dvd_card _)
  apply hfaith G 2 V Y hV (by rw [normalizer_eq_top]; exact le_top) hcore
  rw [generalizedFitting_eq_fitting_of_solvable]
  have hfit : (fittingSubgroup Y).map Y.subtype =
      ⨆ q : (Nat.card Y).primeFactors.attach, (pCore q.val.val Y).map Y.subtype := by
    rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
  rw [hfit]
  apply subgroup_le_centralizer_iSup_of_le_centralizer
  intro q
  have hp : q.val.val.Prime := Nat.prime_of_mem_primeFactors q.val.property
  let : Fact q.val.val.Prime := ⟨hp⟩
  have hqodd : Odd q.val.val := hodd.of_dvd_nat
    (Nat.dvd_of_mem_primeFactors q.val.property)
  have hle : (pCore q.val.val Y).map Y.subtype ≤ pCore q.val.val G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map Y.subtype⟩
  exact (hc _ hqodd).trans (centralizer_le hle)

end CFSG.Quasithin.ChapterA.RankActions

end
