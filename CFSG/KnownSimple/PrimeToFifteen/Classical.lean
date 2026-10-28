module

public import CFSG.KnownSimple.ClassicalModels
public import Theory.SpecificGroups.PrimeToFifteen.Classical.LinearSymplectic
public import Theory.SpecificGroups.PrimeToFifteen.Classical.Orthogonal
public import Theory.SpecificGroups.PrimeToFifteen.Classical.Unitary

/-!
# Three divides every classical catalogue entry

The full six-family catalogue is handled at every admitted rank and field size.
Intrinsic low-rank subgroups provide the factor three, then the catalogue's
actual multiplicative equivalences transport cardinalities. No simplicity or
order formula is assumed. The final known-simple prime-to-15 argument uses this
to eliminate its entire classical alternative, including all low-rank aliases.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1.1.5(3), used in 15.3.34; catalogue ranges are GLS3, §2.7.
-/

public section
namespace CFSG.KnownSimple
open Theory.SpecificGroups.PrimeToFifteen.Classical

/-- The order of every entry in the full classical catalogue is divisible by three. -/
theorem IsClassicalModel.three_dvd_card {G : Type*} [Group G]
    (h : IsClassicalModel G) : 3 ∣ Nat.card G := by
  cases h with
  | linear n q hp iso =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F n hp.2.1
  | unitary n q hp iso =>
    obtain ⟨F, hF, hfin, J, hc, hj, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact unitary_three_dvd J hp.2.1 hp.1 hc hj
  | symplectic r q hp iso =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact symplectic_three_dvd F hp.2.1
  | orthogonalPlus r q hp iso =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact orthogonalPlus_three_dvd F (by have := hp.2; omega)
  | orthogonalOdd r q hp iso =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact orthogonalOdd_three_dvd F hp.2.1
  | orthogonalMinus r q hp iso =>
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := iso
    rw [Nat.card_congr e.toEquiv]
    exact orthogonalMinus_three_dvd F hp.2

/-- The classical branch of the full-catalogue prime-to-15 exclusion. -/
theorem IsClassicalModel.false_of_three_not_dvd {G : Type*} [Group G]
    (h : IsClassicalModel G) (h3 : ¬ 3 ∣ Nat.card G) : False :=
  h3 h.three_dvd_card

end CFSG.KnownSimple
