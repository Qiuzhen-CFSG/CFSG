module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.PSL3.ExtensionBorel
public import Theory.SpecificGroups.SU3.ExtensionBorel.PGU
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The actual extension carriers in A.3.16 and A.3.18

The linear circle group is a subgroup of Aut(PSL₃), obtained by taking the
full preimage of the mixed diagonal--field cyclic subgroup in Out(PSL₃).
The unitary circle group is its centralizer of the graph--field involution.
Neither construction is a semidirect product. The projective general groups
are PGL₃ and the image of the unitary matrices in PGL₃.

We use a noncube diagonal coefficient rather than choose a generator of the
whole field's multiplicative group. For the unitary construction that
coefficient has norm one. This makes the chosen diagonal actor fixed by
graph--field. The signed congruence in A.3.18 restricts the unitary parameter
to odd n. Existence, index, identification of the fixed component with PSU₃,
and nonsplitting are separate mathematical obligations, not fields of these
definitions.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Notation A.3.16 and Lemma A.3.18, printed pp.51--52. The printed order n₃
of the field Sylow subgroup must be (6n)₃: we use the actual Frobenius
power 2n on the field of degree 6n, including n = 1.
-/

@[expose] public section
noncomputable section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter1.Section02.LocalModels

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

universe u

/-- Minus means unitary, as in the existing signed special-group predicates. -/
def SignedCongruence (unitary : Bool) (q : ℕ) : Prop :=
  q % 3 = if unitary then 2 else 1

/-- The order of the cyclic centralizer in A.3.18(3b). -/
def singerOrder (unitary : Bool) (q : ℕ) : ℕ :=
  if unitary then q ^ 2 - q + 1 else q ^ 2 + q + 1

/-- A nontrivial diagonal outer class, expressed at the matrix coefficient. -/
def Noncube {F : Type*} [Field F] (a : Fˣ) : Prop :=
  ∀ b : Fˣ, b ^ 3 ≠ a

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The order-three coefficient actor at the source's degree 6n. -/
def circleField (n : ℕ) : F ≃+* F := (frobeniusEquiv F 2) ^ (2 * n)

/-- The graph--field actor defining the unitary fixed group. -/
def circleGraphField (n : ℕ) : MulAut PSL(3,F) :=
  graph F * fieldAction F ((frobeniusEquiv F 2) ^ (3 * n))

/-- A.3.16's literal preimage in the full automorphism group. -/
def linearCircle (n : ℕ) (a : Fˣ) : Subgroup (MulAut PSL(3,F)) :=
  mixedExtension F (circleField F n) ![a, 1, 1]

/-- A.3.16's graph--field fixed construction, inside the linear extension. -/
def unitaryCircle (n : ℕ) (a : Fˣ) : Subgroup (MulAut PSL(3,F)) :=
  linearCircle F n a ⊓ centralizer ({circleGraphField F n} : Set (MulAut PSL(3,F)))

/-- The marked linear component, with its original inner-automorphism map. -/
def linearCircleComponent (n : ℕ) (a : Fˣ) : Subgroup (linearCircle F n a) :=
  (MulAut.innerSubgroup PSL(3,F)).subgroupOf (linearCircle F n a)

/-- The fixed part of the marked inner component in the unitary construction. -/
def unitaryCircleComponent (n : ℕ) (a : Fˣ) : Subgroup (unitaryCircle F n a) :=
  (MulAut.innerSubgroup PSL(3,F)).subgroupOf (unitaryCircle F n a)

instance linearCircleComponent_normal (n : ℕ) (a : Fˣ) :
    (linearCircleComponent F n a).Normal := inferInstanceAs
      ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (linearCircle F n a)).Normal

instance unitaryCircleComponent_normal (n : ℕ) (a : Fˣ) :
    (unitaryCircleComponent F n a).Normal := inferInstanceAs
      ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (unitaryCircle F n a)).Normal

/-- The original component really lies in the linear circle group. -/
theorem inner_le_linearCircle (n : ℕ) (a : Fˣ) :
    MulAut.innerSubgroup PSL(3,F) ≤ linearCircle F n a :=
  inner_le_mixedExtension F _ _

/-- The source fixed extension is a subgroup of the source linear extension. -/
theorem unitaryCircle_le_linearCircle (n : ℕ) (a : Fˣ) :
    unitaryCircle F n a ≤ linearCircle F n a := inf_le_left

variable {F}

/-- The plus-circle model at q = 2^(6n), using an actual noncube coefficient. -/
def IsLinearCircle (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (n : ℕ), 0 < n ∧ q = 2 ^ (6 * n) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ (6 * n) ∧
      ∃ a : Fˣ, Noncube a ∧ Nonempty (G ≃* linearCircle F n a)

/-- The minus-circle model is the actual graph--field fixed subgroup.
The norm-one diagonal coefficient and odd n retain the source congruence. -/
def IsUnitaryCircle (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (n : ℕ), 0 < n ∧ Odd n ∧ q = 2 ^ (3 * n) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ (6 * n) ∧
      ∃ a : Fˣ, Noncube a ∧ a ^ (q + 1) = 1 ∧
        Nonempty (G ≃* unitaryCircle F n a)

def IsCircleSign (G : Type u) [Group G] (unitary : Bool) (q : ℕ) : Prop :=
  if unitary then IsUnitaryCircle G q else IsLinearCircle G q

/-- Genuine PGL₃, retaining the field cardinality. -/
def IsPGLThree (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* ProjGenLinGroup (Fin 3) F)

/-- Genuine PGU₃: the unitary matrix image in PGL₃. -/
def IsPGUThree (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (G ≃* HermitianForm.ExtensionBorel.projectiveUnitary J)

def IsPGLSign (G : Type u) [Group G] (unitary : Bool) (q : ℕ) : Prop :=
  if unitary then IsPGUThree G q else IsPGLThree G q

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
