module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.SeedGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.DerivedTits

/-!
# The derived Ree carrier and its even order

For positive parameters, the two perfect root seeds generate the full Ree
fixed-point group. Consequently its derived subgroup is the whole group;
the resulting equivalence agrees with the literal subgroup inclusion.
The positive root subgroup of order q^12 proves even order. At parameter
zero we instead use the proved equivalence of the derived subgroup with
Parrott's Tits group, of order 17971200. No identification of the full
binary Ree group with its proper derived subgroup is made.

These bridges connect the full-carrier parabolic calculations of
Aschbacher–Smith F.1.12 with the derived-carrier convention of E.1.14(1),
printed pp.214 and 263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

namespace ReeF4.DerivedCarrier

open Subgroup Parabolics LargeLocalSeeds

/-- Both perfect local seeds lie in the ambient derived subgroup and generate
the carrier. The binary parameter is deliberately excluded. -/
theorem derived_eq_top {m : ℕ} (hm : 0 < m) : commutator (Model m) = ⊤ := by
  have hseed (s : Side) : seed m s ≤ commutator (Model m) := by
    let := OuterLocal.seed_perfect hm s
    rw [← (seed m s).commutator_eq_self]
    exact commutator_mono le_top le_top
  apply top_unique
  rw [← OuterLocal.LargeAutomorphisms.seed_sup_eq_top m]
  exact sup_le (hseed .suzuki) (hseed .linear)

/-- The source derived group is the full fixed-point group when q > 2. -/
def derivedEquiv {m : ℕ} (hm : 0 < m) : commutator (Model m) ≃* Model m :=
  (MulEquiv.subgroupCongr (derived_eq_top hm)).trans Subgroup.topEquiv

@[simp] theorem derivedEquiv_apply {m : ℕ} (hm : 0 < m)
    (x : commutator (Model m)) : derivedEquiv hm x = (x : Model m) := by
  simp [derivedEquiv]

/-- The full fixed-point group has even order, including q = 2. -/
theorem even_card (m : ℕ) : Even (Nat.card (Model m)) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ (unipotent m).card_subgroup_dvd_card
  rw [card_unipotent]
  exact dvd_pow (dvd_pow_self 2 (by omega : 2 * m + 1 ≠ 0)) (by omega)

/-- The exact binary derived order comes from the actual Tits comparison. -/
theorem binary_derived_card : Nat.card (commutator (Model 0)) = 17971200 := by
  obtain ⟨e⟩ := DerivedTits.nonempty_derived_equiv
  exact (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card

/-- Even order in the derived convention, with the Tits endpoint retained. -/
theorem derived_even_card (m : ℕ) : Even (Nat.card (commutator (Model m))) := by
  cases m with
  | zero => rw [binary_derived_card]; decide
  | succ m =>
    rw [Nat.card_congr (derivedEquiv (Nat.succ_pos m)).toEquiv]
    exact even_card (m + 1)

end ReeF4.DerivedCarrier
