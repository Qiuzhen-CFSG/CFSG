module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Statement

/-!
# Individual outstanding model inputs to I.1.3

These contracts separate the concrete kernel calculations from the individual
family rank restrictions. They are inputs to a conditional assembly, not an
assertion of I.1.3. None assumes the multiplier table, Theorem C, or a global
classification. The assembly analyses the full known-simple catalogue and
uses the completed alternating, degree-two, symplectic and G₂ calculations.

Degree-three kernels are requested only for binary fields and odd fields of
prime or prime-square order. Their defining-rank bounds remain explicit;
an ordinary projection kernel alone cannot discharge a kernel field here.
The small G₂ derived carrier is identified with the actual PSU₃(3) model
by the proved Fong comparison, so it requires no separate kernel input.
The seven already proved sporadic exclusions are absent from these inputs.

Source: Aschbacher--Smith I.1.3 and the rank arguments in A.2.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering
universe u

/-- Exactly the degree-three domains supported by the independent kernel work.
No unrestricted odd-field universality is assumed. -/
def DegreeThreeParameters (q : ℕ) : Prop :=
  (∃ n : ℕ, 0 < n ∧ q = 2 ^ n) ∨
    ∃ p f : ℕ, p.Prime ∧ Odd p ∧ (f = 1 ∨ f = 2) ∧ q = p ^ f

/-- Individual unresolved kernel calculations on the original group, always
through its actual model isomorphism. Every value is a group isomorphism. -/
structure KernelInputs (S : Type u) [Group S] [Group.IsPerfect S] : Prop where
  linearThree : ∀ q, DegreeThreeParameters q → q ≠ 2 → q ≠ 4 →
    ClassicalGroup.IsPSL S 3 q →
    (if q % 3 = 1 then Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier)
      else Subsingleton (schurMultiplier S))
  unitaryThree : ∀ q, DegreeThreeParameters q → q ≠ 2 → ClassicalGroup.IsPSU S 3 q →
    (if q % 3 = 2 then Nonempty (schurMultiplier S ≃* MultiplierShape.three.Carrier)
      else Subsingleton (schurMultiplier S))
  linearThreeFour : ClassicalGroup.IsPSL S 3 4 →
    Nonempty (schurMultiplier S ≃* MultiplierShape.exceptionalFortyEight.Carrier)
  g2Four : ClassificationModels.IsG2At S 4 →
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier)
  suzukiEight : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.elementaryFour.Carrier)
  suzukiOther : ∀ m, 1 < m →
    Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
    Subsingleton (schurMultiplier S)
  triality : Triality.Standard.IsTrialityGroup S → Subsingleton (schurMultiplier S)
  reeF4 : ReeF4.IsReeF4Model S → Subsingleton (schurMultiplier S)
  tits : Nonempty (S ≃* Tits.ParrottGroup) → Subsingleton (schurMultiplier S)
  reeDerived : Nonempty (S ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) →
    Subsingleton (schurMultiplier S)
  m11 : Nonempty (S ≃* Sporadic.Mathieu.M11) → Subsingleton (schurMultiplier S)
  m12 : Nonempty (S ≃* Sporadic.Mathieu.M12) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier)
  m22 : Nonempty (S ≃* Sporadic.Mathieu.M22) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.twelve.Carrier)
  m23 : Nonempty (S ≃* Sporadic.Mathieu.M23) → Subsingleton (schurMultiplier S)
  m24 : Nonempty (S ≃* Sporadic.Mathieu.M24) → Subsingleton (schurMultiplier S)
  j1 : Nonempty (S ≃* Janko1.Model) → Subsingleton (schurMultiplier S)
  j2 : Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier)
  j4 : Nonempty (S ≃* Janko4.Model) → Subsingleton (schurMultiplier S)
  hs : Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier)
  he : Nonempty (S ≃* Held.He) → Subsingleton (schurMultiplier S)
  ru : Nonempty (S ≃* Rudvalis.Model) →
    Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier)

/-- Separate source rank/alias obligations on each concrete family. These
are not discharged by surjective section maps alone. -/
structure RankInputs (S : Type u) [Group S] : Prop where
  linear : ∀ n q, KnownSimple.LinearParameters n q → ClassicalGroup.IsPSL S n q →
    n = 2 ∨ n = 3 ∨ (n = 4 ∧ q = 2) ∨ (n = 5 ∧ q = 2)
  linearThree : ∀ q, ClassicalGroup.IsPSL S 3 q → DegreeThreeParameters q
  unitary : ∀ n q, KnownSimple.UnitaryParameters n q → ClassicalGroup.IsPSU S n q →
    n = 2 ∨ n = 3
  unitaryThree : ∀ q, ClassicalGroup.IsPSU S 3 q → DegreeThreeParameters q
  symplectic : ∀ r q, KnownSimple.SymplecticParameters r q → ClassicalGroup.IsPSp S r q →
    (r = 1 ∧ 4 ≤ q) ∨ (r = 2 ∧ ∃ n, 1 < n ∧ q = 2 ^ n)
  orthogonalPlus : ∀ r q, KnownSimple.OrthogonalPlusParameters r q →
    ClassicalGroup.IsPOmegaPlus S r q →
    KnownSimple.LinearParameters 4 q ∧ ClassicalGroup.IsPSL S 4 q
  orthogonalOdd : ∀ r q, KnownSimple.OrthogonalOddParameters r q →
    ClassicalGroup.IsPOmegaOdd S r q →
    (4 ≤ q ∧ ClassicalGroup.IsPSL S 2 q) ∨
      (KnownSimple.SymplecticParameters 2 q ∧ ClassicalGroup.IsPSp S 2 q)
  orthogonalMinus : ∀ r q, KnownSimple.OrthogonalMinusParameters r q →
    ClassicalGroup.IsPOmegaMinus S r q →
    4 ≤ q ^ 2 ∧ ClassicalGroup.IsPSL S 2 (q ^ 2)
  g2 : ∀ q, 2 < q → ClassificationModels.IsG2At S q →
    (∃ n, 2 ≤ n ∧ q = 2 ^ n) ∨ (q.Prime ∧ 3 < q)
  f4 : ∀ q, ¬ ExceptionalGroup.IsF4 S q
  e6 : ∀ q, ¬ ExceptionalGroup.IsE6 S q
  e7 : ∀ q, ¬ ExceptionalGroup.IsE7 S q
  e8 : ∀ q, ¬ ExceptionalGroup.IsE8 S q
  twistedE6 : ∀ q, ¬ ExceptionalGroup.IsTwistedE6 S q
  reeG2 : ∀ q, ¬ ExceptionalGroup.IsReeG2 S q
  co1 : ¬ Nonempty (S ≃* Sporadic.LeechRelated.Co1.Carrier)
  co2 : ¬ Nonempty (S ≃* Sporadic.LeechRelated.Co2.Carrier)
  suz : ¬ Nonempty (S ≃* Sporadic.LeechRelated.Suz.Carrier)
  fi22 : ¬ Nonempty (S ≃* Sporadic.Fischer.Fi22.Carrier)
  fi23 : ¬ Nonempty (S ≃* Sporadic.Fischer.Fi23.Carrier)
  fi24Prime : ¬ Nonempty (S ≃* Sporadic.Fischer.Fi24Prime.Carrier)
  ly : ¬ Nonempty (S ≃* Lyons.LyonsGroup)
  th : ¬ Nonempty (S ≃* Thompson.Model)

end CFSG.Quasithin.ChapterI.SQTKMultipliers
