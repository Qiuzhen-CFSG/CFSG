module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.SharpSplit

/-!
# The retained block and the gluing boundary

After sharpness and strict induction, the unclassified product contains
the distinguished factor and at most one other factor. Its displacement
space must be the actual rotation-moved space, and the complementary
product must fix that space pointwise. These are substantive remaining
claims, not consequences encoded in `PreparedSplit`.

The two conditional contracts separate the small-block argument from
gluing the already classified summands. Their assembly must discharge
both contracts. Source: Aschbacher--Smith G.9.2, printed p.353.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

open DihedralDegree

universe v

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W}
  {i : ι} {exceptional : Prop}

def PreparedSplit.fixedIndices (s : PreparedSplit σ i exceptional) : Finset ι :=
  Finset.univ.erase i \ s.actions.J

def PreparedSplit.retainedIndices (s : PreparedSplit σ i exceptional) : Finset ι :=
  insert i s.actions.J

def PreparedSplit.retainedGroup (s : PreparedSplit σ i exceptional) :
    Subgroup (∀ j, DihedralGroup (p j)) :=
  (subproductHom (p := p) s.retainedIndices).range

/-- The pointwise complementary action and the genuine ordinary block.
In particular the orthogonal alternative includes its group equivalence
and intertwiner; its vector space is the actual displacement span. -/
structure CompletedBlock (s : PreparedSplit σ i exceptional) : Prop where
  fixed_complement : ∀ (g : ∀ j : s.fixedIndices, DihedralGroup (p j))
    (w : rotationMoved (factorRep σ i)), σ (subproductHom s.fixedIndices g) w = (w : W)
  retained_moved : movedSpace σ s.retainedGroup = rotationMoved (factorRep σ i)
  ordinary : IsOrdinaryFactor σ s.retainedGroup

/-- The remaining small-block theorem, uniformly in the already classified
strictly smaller action. Its producer uses the splitting, degree, orthogonal
pair and classified-involution-centralizer inputs. -/
def BlockClassificationTheorem : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ),
    (∀ i, (p i).Prime) → (∀ i, Odd (p i)) →
    ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W],
      ∀ σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W,
        Function.Injective σ → ∀ (i : ι) (exceptional : Prop)
          (s : PreparedSplit σ i exceptional), CompletedBlock s

/-- Append the actual retained factor to the smaller classified family.
The existing count, including any regrouping into orthogonal factors, must
be used, and its exceptional factor must stay at index zero. -/
def AppendClassifiedTheorem : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (i : ι) (exceptional : Prop) (s : PreparedSplit σ i exceptional),
    IsCompl (rotationFixed (factorRep σ i)) (rotationMoved (factorRep σ i)) →
      CompletedBlock s → Nonempty (ClassifiedDecomposition σ ⊤ exceptional)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
