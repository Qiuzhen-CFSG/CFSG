module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.Representation.HexacodeAction.Cover
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition

/-!
# Concrete component models in 13.8.17

Every alternative below is an isomorphism predicate on the group in question.
The primes in Sp₄(q)′ and G₂(q)′ mean the actual commutator subgroups,
including at q = 2. Unitary q is the fixed-field order, so its matrices
are over a field of order q² with conjugation x ↦ x^q.

The carrier for Â₆ is the even hexacode group. The carrier for M̂₂₂ is
the perfect binary matrix core whose projective action on 22 stars has
already been identified with M₂₂ in `CoreRecognition`. In particular it is
not the split product in `Mathieu.M22.Properties.MultiplierCovers`.

`F918Models` records just the classification clause of F.9.18(4), including
its explicit exclusion of Â₇. It is an input specification, not a proof of
F.9.18. The other clauses and the Suzuki exclusion belong to the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(4),
printed pp.325–326; A.3.5–6, p.43; and 13.8.17, p.953 (PDF p.970).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.Models
open Subgroup
open Chapter1.Section02.LocalModels
universe u v

/-- The existing nonsplit hexacode construction of 3.A₆. -/
abbrev A6Triple := Atlas.Codes.HexEvenAutomorphisms

/-- The existing perfect matrix construction of 3.M₂₂. -/
abbrev M22Triple :=
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.derivedGroup

/-- The derived subgroup of the native symplectic matrix group, at every q. -/
def IsSp4DerivedAt (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* commutator (Matrix.symplecticGroup (Fin 2) F))

/-- The derived subgroup of the split-octonion group, including G₂(2)′. -/
def IsG2DerivedAt (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* commutator (Atlas.G2.Model F))

/-- The exact nonabelian range for the signed degree-three family. -/
def ThreeParameter (unitary : Bool) (n : ℕ) : Prop :=
  if unitary then 2 ≤ n else 1 ≤ n

/-- The group-dependent concrete output list of 13.8.17.
The linear cover alternatives retain the A.3.6 congruence condition. -/
inductive ComponentModel (G : Type u) [Group G] : Prop
  | linear_two (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL G 2 (2 ^ n))
  | projective_three (unitary : Bool) (n : ℕ) (hn : ThreeParameter unitary n)
      (iso : IsPSLSign G unitary 3 (2 ^ n))
  | special_three (unitary : Bool) (n : ℕ) (hn : ThreeParameter unitary n)
      (hmod : (2 ^ n) % 3 = if unitary then 2 else 1)
      (iso : IsSLSign G unitary 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 1 ≤ n) (iso : IsSp4DerivedAt G (2 ^ n))
  | g2 (n : ℕ) (hn : 1 ≤ n) (iso : IsG2DerivedAt G (2 ^ n))
  | linear_four (iso : ClassicalGroup.IsPSL G 4 2)
  | linear_five (iso : ClassicalGroup.IsPSL G 5 2)
  | alternating_seven (iso : Nonempty (G ≃* alternatingGroup (Fin 7)))
  | alternating_six_cover (iso : Nonempty (G ≃* A6Triple))
  | mathieu (iso : Nonempty (G ≃* Sporadic.Mathieu.M22))
  | mathieu_cover (iso : Nonempty (G ≃* M22Triple))

/-- The quotient part of F.9.18(4); Mathieu is separately a statement about K*. -/
inductive F918QuotientModel (G : Type u) [Group G] : Prop
  | bender (iso : ClassificationModels.IsBenderModel G)
  | linear_three (n : ℕ) (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL G 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 1 ≤ n) (iso : IsSp4DerivedAt G (2 ^ n))
  | g2 (n : ℕ) (hn : 1 ≤ n) (iso : IsG2DerivedAt G (2 ^ n))
  | linear_four (iso : ClassicalGroup.IsPSL G 4 2)
  | linear_five (iso : ClassicalGroup.IsPSL G 5 2)
  | alternating_seven (iso : Nonempty (G ≃* alternatingGroup (Fin 7)))

/-- Exact model clause of F.9.18(4), with the source's intrinsic cover notation.
Converting that notation to the fixed carriers requires cover uniqueness. -/
def F918Models (G : Type u) [Group G] : Prop :=
  (F918QuotientModel (G ⧸ center G) ∧ ¬ IsAlternatingCover G 7) ∨
    Nonempty (G ≃* Sporadic.Mathieu.M22) ∨ IsM22Cover G

/-- The stage before 13.8.16 removes the Suzuki alternative. -/
def ComponentModelOrSuzuki (G : Type u) [Group G] : Prop :=
  ComponentModel G ∨ ∃ m : ℕ, 1 ≤ m ∧
    Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsSp4DerivedAt.of_mulEquiv {q : ℕ} (h : IsSp4DerivedAt G q) (e : H ≃* G) :
    IsSp4DerivedAt H q := by
  obtain ⟨F, hF, hfin, hq, ⟨a⟩⟩ := h
  exact ⟨F, hF, hfin, hq, ⟨e.trans a⟩⟩

theorem IsG2DerivedAt.of_mulEquiv {q : ℕ} (h : IsG2DerivedAt G q) (e : H ≃* G) :
    IsG2DerivedAt H q := by
  obtain ⟨F, hF, hfin, hq, ⟨a⟩⟩ := h
  exact ⟨F, hF, hfin, hq, ⟨e.trans a⟩⟩

theorem ComponentModel.of_mulEquiv (h : ComponentModel G) (e : H ≃* G) :
    ComponentModel H := by
  cases h with
  | linear_two n hn iso => exact .linear_two n hn (iso.of_mulEquiv e)
  | projective_three unitary n hn iso =>
      apply ComponentModel.projective_three unitary n hn
      cases unitary
      · exact ClassicalGroup.IsPSL.of_mulEquiv iso e
      · exact ClassicalGroup.IsPSU.of_mulEquiv iso e
  | special_three unitary n hn hm iso =>
      apply ComponentModel.special_three unitary n hn hm
      cases unitary
      · obtain ⟨F, hF, hfin, hq, ⟨a⟩⟩ := iso
        exact ⟨F, hF, hfin, hq, ⟨e.trans a⟩⟩
      · obtain ⟨F, hF, hfin, J, hq, hc, ⟨a⟩⟩ := iso
        exact ⟨F, hF, hfin, J, hq, hc, ⟨e.trans a⟩⟩
  | symplectic n hn iso => exact .symplectic n hn (iso.of_mulEquiv e)
  | g2 n hn iso => exact .g2 n hn (iso.of_mulEquiv e)
  | linear_four iso => exact .linear_four (iso.of_mulEquiv e)
  | linear_five iso => exact .linear_five (iso.of_mulEquiv e)
  | alternating_seven iso => exact .alternating_seven (iso.map (e.trans ·))
  | alternating_six_cover iso => exact .alternating_six_cover (iso.map (e.trans ·))
  | mathieu iso => exact .mathieu (iso.map (e.trans ·))
  | mathieu_cover iso => exact .mathieu_cover (iso.map (e.trans ·))

theorem componentModel_mulEquiv_iff (e : G ≃* H) : ComponentModel G ↔ ComponentModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- The parent supplies the genuine Suzuki exclusion of 13.8.16. -/
theorem ComponentModelOrSuzuki.of_no_suzuki (h : ComponentModelOrSuzuki G)
    (hno : ∀ m : ℕ, 1 ≤ m → ¬ Nonempty (G ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : ComponentModel G := by
  rcases h with h | ⟨m, hm, he⟩
  · exact h
  · exact False.elim (hno m hm he)

end CFSG.Quasithin.Chapter13.Section08.Components.Models
