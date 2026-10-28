module

public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Prime-group Fitting subgroups in solvable groups

If the Fitting subgroup of a finite solvable group is a p-group, the
p-complement core is trivial. The two normal subgroups have coprime orders,
so commute and intersect trivially. Self-centralization of the Fitting
subgroup then forces the complement core to be trivial.

This is the solvable Fitting argument used with the Bender method in
GLS2, Chapter F, Section 19.
-/

/-- A solvable group with p-group Fitting subgroup has trivial p-complement
core. -/
public theorem pPrimeCore_eq_bot_of_fitting_isPGroup
    {G : Type*} [Group G] [Finite G] (hG : Group.IsSolvable G)
    (p : ℕ) [Fact p.Prime] (hF : IsPGroup p (fittingSubgroup G)) :
    pPrimeCore p G = ⊥ := by
  obtain ⟨n, hn⟩ := hF.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (pPrimeCore p G))
      (Nat.card (fittingSubgroup G)) := by
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  have hcomm : ⁅pPrimeCore p G, fittingSubgroup G⁆ = ⊥ :=
    bot_unique ((Subgroup.commutator_le_inf
      (H₁ := pPrimeCore p G) (H₂ := fittingSubgroup G)).trans hdisj.eq_bot.le)
  have hle : pPrimeCore p G ≤ fittingSubgroup G :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hG)
  exact bot_unique ((le_inf le_rfl hle).trans hdisj.eq_bot.le)
