module

public import Theory.Representation.RegularCyclicNormalClosure.Basic

/-!
# Goldschmidt–O'Nan pairs

These are the hypotheses and four conclusions of GLS, Number 2, Chapter C,
Definition 14.1 and Proposition 14.2 (`refs/KGroup/GLS2/ChapterC.tex`).
The fixed and moved spaces are the actual subspaces of the given binary
representation. Normalization is required only for elements stabilizing the
fixed space. The TI condition concerns distinct members of its actual orbit.

The source's union notation suppresses zero: in alternative (iii) the union
of the **nonzero** vectors of the orbit members is the complement of the
moved space. These definitions state the problem; they do not assert the
existence of an alternative.
-/

@[expose] public section

namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure

variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual orbit of the fixed subspace under the given representation. -/
def fixedOrbit (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) :
    Set (Submodule (ZMod 2) V) :=
  Set.range fun x : X => (fixedSpace ρ Y).map (ρ x)

/-- Setwise invariance of a subspace under every element of the acting group. -/
def Invariant (ρ : Representation (ZMod 2) X V) (W : Submodule (ZMod 2) V) : Prop :=
  ∀ x : X, W.map (ρ x) = W

/-- Definition 14.1. Finiteness of the group and space is imposed by the theorems. -/
structure Input (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop where
  faithful : Function.Injective ρ
  nontrivial : Y ≠ ⊥
  cyclic : IsCyclic Y
  odd : Odd (Nat.card Y)
  transitive : ∀ v ∈ displacementSpan ρ Y ⊤, v ≠ 0 →
    ∀ w ∈ displacementSpan ρ Y ⊤, w ≠ 0 → ∃ y : Y, ρ y v = w
  fixed_nontrivial : fixedSpace ρ Y ≠ ⊥
  ti : ∀ U ∈ fixedOrbit ρ Y, ∀ W ∈ fixedOrbit ρ Y, U ≠ W → Disjoint U W
  normal_in_stabilizer : ∀ x : X,
    (fixedSpace ρ Y).map (ρ x) = fixedSpace ρ Y →
    Y.map (MulAut.conj x).toMonoidHom = Y

/-- The singleton-orbit alternative. -/
def SingletonCase (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  fixedOrbit ρ Y = {fixedSpace ρ Y} ∧ Invariant ρ (fixedSpace ρ Y)

/-- The two complementary spaces are interchanged by an actual two-element. -/
def SwappedCase (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  fixedOrbit ρ Y = {fixedSpace ρ Y, displacementSpan ρ Y ⊤} ∧
    ∃ t : X, (∃ a : ℕ, orderOf t = 2 ^ a) ∧
      (fixedSpace ρ Y).map (ρ t) = displacementSpan ρ Y ⊤ ∧
      (displacementSpan ρ Y ⊤).map (ρ t) = fixedSpace ρ Y

/-- The orbit covers precisely the vectors outside the invariant moved space. -/
def ComplementCase (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  Nat.card (fixedOrbit ρ Y) = Nat.card (displacementSpan ρ Y ⊤) ∧
    {v : V | v ≠ 0 ∧ ∃ W ∈ fixedOrbit ρ Y, v ∈ W} =
      {v : V | v ∉ displacementSpan ρ Y ⊤} ∧
    Invariant ρ (displacementSpan ρ Y ⊤)

/-- The exceptional dimensions and the nonabelian group of order 21. -/
def ExceptionalCase (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1 ∧
    Module.finrank (ZMod 2) V = 3 ∧ Nat.card X = 21 ∧
    ¬ ∀ x y : X, x * y = y * x

/-- All four conclusions of Proposition 14.2, retaining the given group and action. -/
def Alternatives (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  SingletonCase ρ Y ∨ SwappedCase ρ Y ∨ ComplementCase ρ Y ∨ ExceptionalCase ρ Y

/-- Transitivity on all nonzero vectors, used in the exceptional branch of the proof. -/
def NonzeroTransitive (ρ : Representation (ZMod 2) X V) : Prop :=
  ∀ v : V, v ≠ 0 → ∀ w : V, w ≠ 0 → ∃ x : X, ρ x v = w

/-- The union of the nonzero vectors in the Y-images of one subspace. -/
def nonzeroSuborbitUnion (ρ : Representation (ZMod 2) X V) (Y : Subgroup X)
    (W : Submodule (ZMod 2) V) : Set V :=
  {v | v ≠ 0 ∧ ∃ y : Y, v ∈ W.map (ρ y)}

/-- The local dichotomy of Step 1, as a contract for the orbit-geometry proof.
It describes the actual suborbit unions and the actual stabilizer action.
This is a derived proof-step target, not an input to Definition 14.1. -/
def SuborbitGeometry (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  ∀ W ∈ fixedOrbit ρ Y, W ≠ fixedSpace ρ Y →
    (W ≤ displacementSpan ρ Y ⊤ ∧
      nonzeroSuborbitUnion ρ Y W = {v | v ∈ displacementSpan ρ Y ⊤ ∧ v ≠ 0} ∧
      ∀ v ∈ W, v ≠ 0 → ∀ w ∈ W, w ≠ 0 →
        ∃ y : Y, W.map (ρ y) = W ∧ ρ y v = w) ∨
    (Disjoint W (displacementSpan ρ Y ⊤) ∧
      (∀ y : Y, W.map (ρ y) = W → y = 1) ∧
      nonzeroSuborbitUnion ρ Y W =
        {v | v ∉ fixedSpace ρ Y ∧ v ∉ displacementSpan ρ Y ⊤})

/-- The geometric conclusions of Steps 1–2 when the first three cases fail. -/
def TransitiveGeometry (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) : Prop :=
  NonzeroTransitive ρ ∧ Odd (Nat.card (fixedOrbit ρ Y)) ∧
    Nat.card (fixedSpace ρ Y) ^ 2 ≤ Nat.card (displacementSpan ρ Y ⊤)

/-- The induction hypothesis used in Step 3, restricted to proper subgroups.
This is a proof-step hypothesis, not part of Definition 14.1. -/
def ProperSubgroupCases (ρ : Representation (ZMod 2) X V) : Prop :=
  ∀ H : Subgroup X, H ≠ ⊤ → ∀ C : Subgroup H,
    Input (ρ.comp H.subtype) C → Alternatives (ρ.comp H.subtype) C

end Representation.GoldschmidtONan
