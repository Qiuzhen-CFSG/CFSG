module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow.Arithmetic
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow.NaturalAction
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.CubicTorus
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# Cyclic cyclotomic Sylow subgroups of even-characteristic G₂

For q > 4 even and a prime r > 3 dividing |G₂(q)| but not q²−1, the order
formula puts r in q²+q+1 or q²−q+1. In the first case the cubic norm-one
torus has index prime to r and supplies a cyclic Sylow subgroup. In the
second case q has order six modulo r. The faithful six-dimensional natural
action makes a central order-r subgroup of a Sylow subgroup irreducible;
the whole Sylow subgroup embeds in its finite endomorphism field and is
cyclic. Thus no simultaneous finite-field torus placement is assumed.

Cyclic-Sylow transfer then excludes r from the literal kernel of the
canonical universal perfect central cover of the octonion model.

Source: Aschbacher--Smith I.1.2--I.1.4, printed pp.407--408 (PDF pp.418--419),
and the multiplier calculation cited in GLS III §6.1. The cubic torus is
reused from the characteristic-independent part of the odd-prime development.
The octonion model is the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The cubic norm-one torus contains a full Sylow subgroup at these primes. -/
theorem sylow_isCyclic_of_dvd_cubic {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hd : r ∣ Nat.card F ^ 2 + Nat.card F + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  obtain ⟨C, hcyclic, hc⟩ := OddCyclotomicSylow.exists_cubic_torus F 2
  let := hcyclic
  exact sylow_isCyclic_of_cubic_torus hr hquad hd C hc Q

/-- In the twisted cubic branch, the faithful natural action places the
whole Sylow subgroup in the units of a finite endomorphism field. -/
theorem sylow_isCyclic_of_dvd_twisted (hF : 4 < Nat.card F)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hd : r ∣ Nat.card F ^ 2 - Nat.card F + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  let := Fintype.ofFinite F
  have hrF : (r : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F (Fact.out : r.Prime) (by omega : 2 ≠ r)
  have hq : ¬ r ∣ Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using not_dvd_card_field (F := F) hr
  apply Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree
    Q.isPGroup' hrF hq ((Natural.action F).comp (Q : Subgroup (Model F)).subtype)
    ((natural_action_injective (by omega)).comp (Q : Subgroup (Model F)).subtype_injective)
  rw [Natural.finrank_space, ← Nat.card_eq_fintype_card, orderOf_card_of_dvd_twisted hr hquad hd]

/-- Every cyclotomic Sylow subgroup in the source range is cyclic. -/
theorem sylow_isCyclic (hF : 4 < Nat.card F) {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hquad : ¬ r ∣ Nat.card F ^ 2 - 1)
    (horder : r ∣ Nat.card (Model F)) (Q : Sylow r (Model F)) : IsCyclic Q := by
  rcases cyclotomic_alternatives hr hquad horder with h3 | h6
  · exact sylow_isCyclic_of_dvd_cubic hr hquad h3 Q
  · exact sylow_isCyclic_of_dvd_twisted hF hr hquad h6 Q

/-- I.1.2 applied to the actual canonical cover in both cyclotomic branches. -/
theorem not_dvd_card_universal_kernel (hF : 4 < Nat.card F)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (hquad : ¬ r ∣ Nat.card F ^ 2 - 1) (horder : r ∣ Nat.card (Model F)) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic hF hr hquad horder)

end Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
