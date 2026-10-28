module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.BinaryOffender.CubicRatio
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The source domain and independent representation inputs for K.2

Theorem C's odd-characteristic family consists of PSL₂(p), PSL₂(p²),
PSL₃(p), and PSU₃(p), with p an odd prime. The unitary parameter is the
fixed-field order: its coefficient field has order p². All models below
are actual central-quotient isomorphisms.

The two restriction propositions specify the representation-theoretic work
owned by `qt-b01-ff-odd-linear-parameters` and
`qt-b01-ff-odd-unitary-parameters`. They are explicit inputs, not asserted
theorems. They concern the original ambient action, allowing central covers
and outer automorphisms. In particular their threshold is two, not the FF
threshold one. The source-family assembly is in `OddCharacteristic`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.2,
printed p.453 (PDF p.464), citing Guralnick–Malle [GM02].
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.OddCharacteristic

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped ENNReal

/-- Exactly the three linear parameter families in K.2. -/
inductive LinearParameters : ℕ → ℕ → Prop
  | prime (p : ℕ) (prime : p.Prime) (odd : Odd p) : LinearParameters 2 p
  | square (p : ℕ) (prime : p.Prime) (odd : Odd p) : LinearParameters 2 (p ^ 2)
  | degreeThree (p : ℕ) (prime : p.Prime) (odd : Odd p) : LinearParameters 3 p

/-- The literal existing odd-characteristic alternative supplied by Theorem C. -/
abbrev SourceFamily (Q : Type*) [Group Q] : Prop :=
  ChapterA.Section02.IsTheoremCOddModel Q

/-- The actual field model rules out exponent zero in Theorem C's displayed
bound e ≤ 2, giving exactly the two PSL₂ parameter families in K.2. -/
theorem linearParameters_of_prime_power_model {Q : Type*} [Group Q]
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL Q 2 (p ^ e)) : LinearParameters 2 (p ^ e) := by
  have he0 : e ≠ 0 := by
    intro he0
    obtain ⟨F, _, _, hc, _⟩ := hm
    have hlt : 1 < Nat.card F := Finite.one_lt_card
    simp only [he0, pow_zero] at hc
    omega
  have he12 : e = 1 ∨ e = 2 := by omega
  rcases he12 with rfl | rfl
  · simpa only [pow_one] using LinearParameters.prime p hp ho
  · exact LinearParameters.square p hp ho

universe u v
variable {G : Type u} {V : Type v} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual Chapter K hypotheses, with the original ambient representation
and its restriction to the specified generalized Fitting subgroup. -/
structure SourceHypotheses (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  generalizedFitting_eq : L = generalizedFitting G
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp L.subtype)

/-- The linear GM02 restriction on a fixed ambient action. This proposition
must be proved by the linear producer before unconditional K.2 assembly. -/
def LinearRestriction (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  SourceHypotheses ρ L → ∀ {n q : ℕ}, LinearParameters n q →
    ClassicalGroup.IsPSL (L ⧸ center L) n q → cubicRatio ρ ≤ 2 →
    n = 2 ∧ (q = 5 ∨ q = 7 ∨ q = 9)

/-- The unitary GM02 restriction on the same ambient action. The input is
PSU₃(p), not a group over a coefficient field of order p. -/
def UnitaryRestriction (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  SourceHypotheses ρ L → ∀ {p : ℕ}, p.Prime → Odd p →
    ClassicalGroup.IsPSU (L ⧸ center L) 3 p → cubicRatio ρ ≤ 2 → p = 3

end CFSG.Quasithin.ChapterK.OddCharacteristic
