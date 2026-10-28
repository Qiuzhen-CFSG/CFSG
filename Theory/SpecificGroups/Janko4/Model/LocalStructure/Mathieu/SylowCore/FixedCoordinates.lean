module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData
public import Theory.ElementaryAbelian.Basic

/-!
# The finite coordinate bound for the max1 Sylow calculation

The pair labels identify the eleven basis vectors of the binary kernel.
Permuting their endpoints gives the image rows of a binary coordinate map;
`maskImage` XORs the selected rows. Since `StarGroup` uses the left-conjugation
generators, these are left-conjugation coordinates, not dual coordinates.

`FixedMasks` is the actual set of masks fixed by every element of the supplied
subgroup of the certified Sylow candidate. `NormalElementaryFixedBound` is
the finite inequality still to be proved. Its transport to the local kernel
also requires a proof; neither definition asserts a matrix-action comparison.

The tables come from the ATLAS max1 words documented in `Cardinality.Subgroup`
and the kernel/star comparison documented in `Image.StarData`.
-/

@[expose] public section

namespace Janko4.LocalStructure.SylowCore
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

/-- Row-coordinate evaluation from the images of the eleven marked basis pairs. -/
def starMask (g : StarGroup) (m : ℕ) : ℕ :=
  maskImage (fun i => pairLabel (g.val (basisPair i).1) (g.val (basisPair i).2)) m

/-- Bounded binary masks fixed by the whole subgroup, with no dualization. -/
def FixedMasks (B : Subgroup sylowCandidate) : Type :=
  {m : Fin 2048 // ∀ b : B, starMask b.val.val m.val = m.val}

/-- The strict size gap needed for uniqueness of the elementary kernel.
This is a finite proof obligation, not a certificate assumed to exist. -/
def NormalElementaryFixedBound : Prop :=
  ∀ B : Subgroup sylowCandidate, B.Normal → IsElementaryAbelian 2 B → B ≠ ⊥ →
    Nat.card B * Nat.card (FixedMasks B) ≤ 1024

end Janko4.LocalStructure.SylowCore
