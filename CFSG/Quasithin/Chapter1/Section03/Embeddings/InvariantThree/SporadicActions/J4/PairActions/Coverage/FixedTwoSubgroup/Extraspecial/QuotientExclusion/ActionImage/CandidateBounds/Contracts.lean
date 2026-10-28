module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateBounds.Data
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.CandidateBounds.Profiles

/-!
# Independent contracts for the candidate profile calculation

The ordinary rows need two independent certificates: actual quotient
coordinates preserving the finite coloring, and the order bound on that
coloring's stabilizer. Four exceptional rows retain all of the original
Sylow, normalizer, index, and radical hypotheses.

None of these contracts is assumed to be inhabited. The assembly module
must discharge all three before proving the requested candidate theorem.
Source context: Aschbacher–Smith 1.3.4, printed p.511/PDF p.528.
-/

@[expose] public section

open Subgroup Janko4.OuterReduction.OddIndex

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
namespace ActionImageCandidates.ProfileBounds

/-- Genuine coordinates and color preservation on the actual candidate quotient. -/
structure Realization (i : Fin 193) where
  coordinates : (candidate i ⧸ frattini (candidate i)) ≃* Binary i
  invariant : ∀ (f : MulAut (candidate i)) v,
    color i (MulAut.congr coordinates (quotientAut (frattini (candidate i)) f) v) = color i v

/-- Concrete group calculations required for the 189 ordinary rows. -/
def Realizations : Prop :=
  ∀ i : Fin 193, i ∉ exceptional → Nonempty (Realization i)

/-- Purely finite linear-stabilizer calculations, independent of the J₄ comparisons. -/
def StabilizerBounds : Prop :=
  ∀ i : Fin 193, i ∉ exceptional → ¬ 27 ∣ Nat.card (colorStabilizer (color i))

/-- The four exceptional rows keep every hypothesis of the requested action bound. -/
def ExceptionalBounds : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ i : Fin 193, i ∈ exceptional →
      twoSubgroup ≤ normalizer (candidate i : Set Janko4.Model) →
      (candidate i).relIndex twoSubgroup ≤ 32 →
      (candidate i).IsPRadical 2 →
      ¬ 27 ∣ Nat.card (fixedTwoFrattiniAction (candidate i)).range

end ActionImageCandidates.ProfileBounds
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

