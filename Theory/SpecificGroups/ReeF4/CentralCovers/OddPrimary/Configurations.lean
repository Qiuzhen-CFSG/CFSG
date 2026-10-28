module

public import Theory.SpecificGroups.ReeF4.Model
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Odd local configurations in the actual Ree group

The abelian case uses two commuting Sylow generators and an ambient element
that either exchanges them or inverts the first while fixing the second.
The three-primary case instead allows a cyclic supplement to the torus:
an ambient inverter must fix that supplement. These are equations in the
literal exceptional fixed subgroup, with no covering or multiplier premise.

Constructing these configurations is a separate geometric obligation. In
particular, an abstract torus of the right order does not supply its embedding,
Sylow status, or ambient conjugation action. The three-primary torus is allowed
to have arbitrary three-power exponent. The family constructors must use
`1 ≤ m`; no identification of `Model 0` with the Tits group is intended.

Sources: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`; GLS3 §6.1, with the exceptional fixed-point and torus
conventions in §2.2 and Example 2.6.3 of `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

open Subgroup

/-- A pair action reversing its commutator in a central extension. Both
alternatives require an element of the actual finite Ree group. -/
@[expose] def ReversesPair {m : ℕ} (x y : Model m) : Prop :=
  (∃ r : Model m, r * x * r⁻¹ = y ∧ r * y * r⁻¹ = x) ∨
  (∃ r : Model m, r * x * r⁻¹ = x⁻¹ ∧ Commute r y)

/-- The abelian Sylow configuration used at primes greater than three. -/
structure AbelianSylowData (m p : ℕ) where
  sylow : Sylow p (Model m)
  first : Model m
  second : Model m
  generated : closure ({first, second} : Set (Model m)) = (sylow : Subgroup (Model m))
  generators_commute : Commute first second
  reverses : ReversesPair first second

/-- The geometry required at a prime greater than three. Cyclic Sylow
subgroups need no normalizer witness; noncyclic ones use a marked pair. -/
@[expose] def GoodPrimeGeometry (m p : ℕ) : Prop :=
  (∀ P : Sylow p (Model m), IsCyclic P) ∨ Nonempty (AbelianSylowData m p)

/-- The nonabelian three-primary configuration, with no exponent-three
restriction on the torus and no assumption about lifts. -/
structure ThreeSylowData (m : ℕ) where
  sylow : Sylow 3 (Model m)
  torus : Subgroup (Model m)
  first : Model m
  second : Model m
  cycle : Model m
  swap : Model m
  inverter : Model m
  torus_generated : closure ({first, second} : Set (Model m)) = torus
  generators_commute : Commute first second
  swap_first : swap * first * swap⁻¹ = second
  swap_second : swap * second * swap⁻¹ = first
  sylow_generated : torus ⊔ zpowers cycle = (sylow : Subgroup (Model m))
  cycle_normalizes : cycle ∈ normalizer (torus : Set (Model m))
  inverts_torus : ∀ t ∈ torus, inverter * t * inverter⁻¹ = t⁻¹
  fixes_cycle : Commute inverter cycle

end ReeF4.CentralCovers.OddPrimary
