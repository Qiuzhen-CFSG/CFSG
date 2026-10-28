module

public import GorensteinWalter.Section2.Bender1970_16
public import Theory.GroupTheory.Fitting.PGroup

/-!
# Bender uniqueness with incompatible prime cores

Two maximal subgroups with mutual generalized-Fitting containment coincide
if the first is solvable with nontrivial p-complement core and the second
has nontrivial p-core. Otherwise Bender's theorem makes both generalized
Fitting subgroups q-groups. The second p-core forces q = p, contradicting
the solvable Fitting self-centralization theorem in the first subgroup.
The same contradiction applies when p divides the order of the first
Fitting subgroup; no hypothesis on the second p-core is then needed.

Source: GLS2, Chapter F, Theorem 19.1, and Bender (1970), Statement 1.6.
-/

namespace GorensteinWalter

/-- Solvable subgroups have no quasisimple components. -/
public theorem componentLayerOf_eq_bot_of_solvable
    {G : Type*} [Group G] (M : Subgroup G) (hM : Group.IsSolvable M) :
    componentLayerOf M = ⊥ := by
  apply bot_unique
  refine sSup_le fun E hE => ?_
  let _ := hM
  have hsolv : Group.IsSolvable E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hE.1)
  let _ : Nontrivial E := hE.2.2.1
  let _ : Group.IsPerfect E := Group.isPerfect_def.mpr hE.2.2.2.1
  exact (Group.IsPerfect.not_isSolvable E hsolv).elim

/-- For a solvable subgroup the generalized Fitting subgroup is its Fitting
subgroup. -/
public theorem generalizedFittingSubgroupOf_eq_fittingSubgroupOf_of_solvable
    {G : Type*} [Group G] (M : Subgroup G) (hM : Group.IsSolvable M) :
    generalizedFittingSubgroupOf M = fittingSubgroupOf M := by
  rw [generalizedFittingSubgroupOf, componentLayerOf_eq_bot_of_solvable M hM, sup_bot_eq]

/-- The prime-core obstruction to a distinct Bender pair. -/
public theorem maximal_eq_of_mutual_fitting_and_incompatible_cores
    {G : Type*} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (M N : Subgroup G) (hM : IsCoatom M) (hN : IsCoatom N)
    (hsolv : Group.IsSolvable M) (p : ℕ) [Fact p.Prime]
    (hodd : pPrimeCore p M ≠ ⊥) (hcore : pCore p N ≠ ⊥)
    (hFMN : generalizedFittingSubgroupOf M ≤ N)
    (hFNM : generalizedFittingSubgroupOf N ≤ M) : M = N := by
  by_contra hne
  obtain ⟨q, hq, hMq, hNq⟩ := bender1970_1_6_maximalSubgroups_pGroups
    hsimple M N hM hN hne hFMN hFNM
  let _ : Fact q.Prime := ⟨hq⟩
  have hPNq : IsPGroup q (pCore p N) :=
    (hNq.to_le ((Subgroup.map_mono (f := N.subtype) (pCore_le_fitting N p)).trans
      le_sup_left)).of_equiv
        (Subgroup.equivMapOfInjective (pCore p N) N.subtype N.subtype_injective).symm
  have hpdvd : p ∣ Nat.card (pCore p N) :=
    (pCore_isPGroup (p := p) (G := N)).card_eq_or_dvd.resolve_left
      (fun h => hcore (Subgroup.card_eq_one.mp h))
  obtain ⟨n, hn⟩ := hPNq.exists_card_eq
  have hpq : p = q := Nat.prime_eq_prime_of_dvd_pow Fact.out hq (hn ▸ hpdvd)
  subst q
  have hFM : IsPGroup p (fittingSubgroup M) :=
    (hMq.to_le (le_sup_left : fittingSubgroupOf M ≤
      generalizedFittingSubgroupOf M)).of_equiv
        (Subgroup.equivMapOfInjective (fittingSubgroup M) M.subtype
          M.subtype_injective).symm
  exact hodd (pPrimeCore_eq_bot_of_fitting_isPGroup hsolv p hFM)

/-- For solvable maximal subgroups it suffices to check ordinary Fitting
containments. -/
public theorem maximal_eq_of_solvable_mutual_fitting_and_incompatible_cores
    {G : Type*} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (M N : Subgroup G) (hM : IsCoatom M) (hN : IsCoatom N)
    (hsolvM : Group.IsSolvable M) (hsolvN : Group.IsSolvable N)
    (p : ℕ) [Fact p.Prime]
    (hodd : pPrimeCore p M ≠ ⊥) (hcore : pCore p N ≠ ⊥)
    (hFMN : fittingSubgroupOf M ≤ N) (hFNM : fittingSubgroupOf N ≤ M) : M = N := by
  apply maximal_eq_of_mutual_fitting_and_incompatible_cores hsimple M N hM hN
    hsolvM p hodd hcore
  · rwa [generalizedFittingSubgroupOf_eq_fittingSubgroupOf_of_solvable M hsolvM]
  · rwa [generalizedFittingSubgroupOf_eq_fittingSubgroupOf_of_solvable N hsolvN]

/-- If p divides the first Fitting subgroup and its p-complement core is
nontrivial, mutual Fitting containment forces equality. This version does
not require any prime-core information about the second maximal subgroup. -/
public theorem maximal_eq_of_solvable_mutual_fitting_of_fitting_card_dvd
    {G : Type*} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (M N : Subgroup G) (hM : IsCoatom M) (hN : IsCoatom N)
    (hsolvM : Group.IsSolvable M) (hsolvN : Group.IsSolvable N)
    (p : ℕ) [Fact p.Prime] (hodd : pPrimeCore p M ≠ ⊥)
    (hdiv : p ∣ Nat.card (fittingSubgroup M))
    (hFMN : fittingSubgroupOf M ≤ N) (hFNM : fittingSubgroupOf N ≤ M) : M = N := by
  by_contra hne
  have hFMN' : generalizedFittingSubgroupOf M ≤ N := by
    rwa [generalizedFittingSubgroupOf_eq_fittingSubgroupOf_of_solvable M hsolvM]
  have hFNM' : generalizedFittingSubgroupOf N ≤ M := by
    rwa [generalizedFittingSubgroupOf_eq_fittingSubgroupOf_of_solvable N hsolvN]
  obtain ⟨q, hq, hMq, -⟩ := bender1970_1_6_maximalSubgroups_pGroups
    hsimple M N hM hN hne hFMN' hFNM'
  let : Fact q.Prime := ⟨hq⟩
  have hFMq : IsPGroup q (fittingSubgroup M) :=
    (hMq.to_le (le_sup_left : fittingSubgroupOf M ≤
      generalizedFittingSubgroupOf M)).of_equiv
        (Subgroup.equivMapOfInjective (fittingSubgroup M) M.subtype
          M.subtype_injective).symm
  obtain ⟨n, hn⟩ := hFMq.exists_card_eq
  have hpq : p = q := Nat.prime_eq_prime_of_dvd_pow Fact.out hq (hn ▸ hdiv)
  subst q
  exact hodd (pPrimeCore_eq_bot_of_fitting_isPGroup hsolvM p hFMq)

end GorensteinWalter
