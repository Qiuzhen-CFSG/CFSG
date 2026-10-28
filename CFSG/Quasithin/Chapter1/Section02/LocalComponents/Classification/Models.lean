module

public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.ReeF4.LocalBlockInput
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Mathlib.GroupTheory.Frattini

/-!
# Models for A.3.6 and A.3.12

These are mathematical isomorphism predicates, not recognition theorems.
Theorem C has its own complete list: it includes A₇ and the odd-characteristic
families, and excludes U₄, U₅ and J₃. Small derived groups use their actual
commutator carriers, without assuming exceptional isomorphisms.

The general Ree alternative uses the fixed subgroup of an endomorphism of the
concrete split F₄ group satisfying every prescribed exceptional root equation.
Existence of that endomorphism is not asserted here. A witness to the model
predicate includes that construction input and an actual isomorphism.

The notation X/Y in A.3.12 specifies a normal kernel Y and quotient X; it does
not assert a splitting. Triple covers are perfect groups with the specified
central quotient and cyclic center of order three. Natural-module assertions
include an intertwining identity for the actual conjugation action.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Theorem C and
Remark A.2.4 (p.33), A.3.5–A.3.6 (pp.43–45), A.3.12 (pp.47–48).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter1.Section02.LocalModels
open Subgroup Theory.GroupTheory
open ClassificationModels
universe u

def IsAlternating (G : Type u) [Group G] (n : ℕ) : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin n))

def IsSL (G : Type u) [Group G] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin n) F)

def IsSU (G : Type u) [Group G] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (J : BenderSuzuki.MatrixGroups.HermitianForm n F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (G ≃* J.specialSubgroup)

/-- `unitary = true` denotes the minus sign in the source's epsilon notation. -/
def IsSLSign (G : Type u) [Group G] (unitary : Bool) (n q : ℕ) : Prop :=
  if unitary then IsSU G n q else IsSL G n q

def IsPSLSign (G : Type u) [Group G] (unitary : Bool) (n q : ℕ) : Prop :=
  if unitary then ClassicalGroup.IsPSU G n q else ClassicalGroup.IsPSL G n q

/-- A perfect central three-cover, with an actual isomorphism of its quotient. -/
def IsThreeCover (G : Type u) [Group G] (S : Type) [Group S] : Prop :=
  IsQuasisimple G ∧ Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((G ⧸ center G) ≃* S)

def IsAlternatingCover (G : Type u) [Group G] (n : ℕ) : Prop :=
  IsThreeCover G (alternatingGroup (Fin n))

def IsM22Cover (G : Type u) [Group G] : Prop :=
  IsThreeCover G Sporadic.Mathieu.M22

/-- The exceptional twist is specified on the actual split root generators. -/
def IsReeF4At (G : Type u) [Group G] (m : ℕ) : Prop :=
  ∃ d : ReeF4.LocalBlockInput m, Nonempty (G ≃* d.fixedGroup)

/-- Exactly the rank-two characteristic-two families in Remark A.2.4(C.3). -/
inductive RankTwoTheoremC (G : Type u) [Group G] : Prop
  | linear (f : ℕ) (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSL G 3 (2 ^ f))
  | symplectic (f : ℕ) (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSp G 2 (2 ^ f))
  | g2 (f : ℕ) (hf : 2 ≤ f) (iso : IsG2At G (2 ^ f))
  | triality (f : ℕ) (hf : 1 ≤ f)
      (iso : Triality.Standard.IsTrialityGroupAt (2 ^ f) G)
  | ree (m : ℕ) (hm : 1 ≤ m) (iso : IsReeF4At G m)
  | symplectic_derived
      (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2_derived (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (iso : Nonempty (G ≃* Tits.ParrottGroup))

/-- The full SQTK list of Theorem C, as distinct from the QTKE list. -/
inductive TheoremCModel (G : Type u) [Group G] : Prop
  | alternating (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (iso : IsAlternating G n)
  | linear_odd (p e : ℕ) (hp : p.Prime) (ho : Odd p)
      (he : e = 1 ∨ e = 2) (hsimple : 4 ≤ p ^ e)
      (iso : ClassicalGroup.IsPSL G 2 (p ^ e))
  | three_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
      (iso : IsPSLSign G unitary 3 p)
  | rank_one (iso : IsBenderModel G)
  | rank_two (iso : RankTwoTheoremC G)
  | binary_linear (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | sporadic (name : SporadicName) (hne : name ≠ .j3)
      (iso : Nonempty (G ≃* name.Carrier))
  | janko_one (iso : Nonempty (G ≃* Janko1.Model))

/-- The common classical parameter condition for A.3.6(2). -/
def CoverParameter (unitary : Bool) (q : ℕ) : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ q = 2 ^ e ∧ q % 3 = if unitary then 2 else 1) ∨
    (q.Prime ∧ Odd q)

inductive ThreeCoverModel (G : Type u) [Group G] : Prop
  | classical (unitary : Bool) (q : ℕ) (hq : CoverParameter unitary q)
      (iso : IsSLSign G unitary 3 q)
  | alternating_six (iso : IsAlternatingCover G 6)
  | alternating_seven (iso : IsAlternatingCover G 7)
  | mathieu (iso : IsM22Cover G)

/-- The parameter wording printed in 1.2.1(4b), where the center condition
is stated separately and the mod-three restriction is no longer displayed. -/
inductive ChapterOneThreeCoverModel (G : Type u) [Group G] : Prop
  | classical (unitary : Bool) (q : ℕ)
      (hq : (∃ e : ℕ, 1 ≤ e ∧ q = 2 ^ e) ∨ (q.Prime ∧ Odd q))
      (iso : IsSLSign G unitary 3 q)
  | alternating_six (iso : IsAlternatingCover G 6)
  | alternating_seven (iso : IsAlternatingCover G 7)
  | mathieu (iso : IsM22Cover G)

theorem ThreeCoverModel.toChapterOne {G : Type u} [Group G]
    (h : ThreeCoverModel G) : ChapterOneThreeCoverModel G := by
  cases h with
  | classical unitary q hq iso =>
      apply ChapterOneThreeCoverModel.classical unitary q ?_ iso
      rcases hq with ⟨e, he, hq, _⟩ | hq
      · exact Or.inl ⟨e, he, hq⟩
      · exact Or.inr hq
  | alternating_six iso => exact .alternating_six iso
  | alternating_seven iso => exact .alternating_seven iso
  | mathieu iso => exact .mathieu iso

/-- An elementary abelian group of order `p^r`, with its concrete coordinates. -/
def ElementaryModel (p r : ℕ) (G : Type u) [Group G] : Prop :=
  Nonempty (G ≃* Multiplicative (Fin r → ZMod p))

/-- Homocyclic of rank two, with positive exponent. -/
def HomocyclicTwo (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ Nonempty (G ≃* Multiplicative (Fin 2 → ZMod (p ^ a)))

/-- Extraspecial of the specified order; the source does not specify a sign. -/
def ExtraspecialModel (p n : ℕ) (G : Type u) [Group G] : Prop :=
  IsExtraspecial p G ∧ Nat.card G = p ^ (1 + 2 * n)

/-- For odd primes the source's `p^(1+2)` additionally specifies exponent p
(Notation on p.25, and the index entry on p.471). -/
def OddExtraspecialThree (p : ℕ) (G : Type u) [Group G] : Prop :=
  ExtraspecialModel p 1 G ∧ ∀ x : G, x ^ p = 1

/-- A central product `Z₄ * 2^(1+2n)`, expressed internally with exact overlap. -/
def CyclicFourCentralProduct (n : ℕ) (G : Type u) [Group G] : Prop :=
  ∃ C E : Subgroup G,
    Nonempty (C ≃* Multiplicative (ZMod 4)) ∧ ExtraspecialModel 2 n E ∧
    C ⊔ E = ⊤ ∧ ⁅C, E⁆ = ⊥ ∧ C ⊓ E = (center E).map E.subtype

/-- The source's extension notation, with a normal kernel and actual quotient. -/
def HasExtension (G : Type u) [Group G] (kernel quotient : GroupClass.{u}) : Prop :=
  ∃ N : Subgroup G, ∃ _ : N.Normal, kernel N ∧ quotient (G ⧸ N)

/-- The conjugation action of `G/N` on `N` is the two-dimensional natural action.
The identity includes every element of `G`, so it also asserts that `N` acts
trivially on itself, as required for this quotient action. -/
def NaturalSL2Action (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    ∃ (v : N ≃* Multiplicative (Fin 2 → F))
      (ρ : (G ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ (g : G) (x : N),
        v ⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x x.property g⟩ =
          Multiplicative.ofAdd
            (Matrix.mulVec (ρ (QuotientGroup.mk' N g)).val (Multiplicative.toAdd (v x)))

end CFSG.Quasithin.Chapter1.Section02.LocalModels
