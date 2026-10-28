module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Remaining branches of the full quotient catalogue

The odd-characteristic and Bender branches ask only for an intrinsic
involution-centralizer calculation on the actual simple quotient. The
rank-two and sporadic branches retain the full source configuration:
Sp₄(4) has a field involution with fixed A₆ component, and HS has an inner
involution with such a component. Thus an unrestricted fixed-component
exclusion would be incorrect for these two branches.

These are outstanding proof obligations, not assumed source results.
The importing quotient-recognition module retains their final assembly.
All models are the actual equivalence predicates of the full Theorem C.

Source: Aschbacher–Smith, Theorem C, printed p.33, E.6.8, pp.247–248,
and E.6.23, p.254 (combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
universe u

/-- The prime-field restrictions in C(2) rule out a fixed A₆ component. -/
def OddFixedComponentExclusion : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    ChapterA.Section02.IsTheoremCOddModel D →
    ∀ a : MulAut D, orderOf a = 2 → ∀ S : Subgroup D,
      IsComponentIn S a.fixedSubgroup → ¬ Nonempty (S ≃* alternatingGroup (Fin 6))

/-- The three characteristic-two rank-one families have no fixed A₆ component. -/
def BenderFixedComponentExclusion : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
    ClassificationModels.IsBenderModel D →
    ∀ a : MulAut D, orderOf a = 2 → ∀ S : Subgroup D,
      IsComponentIn S a.fixedSubgroup → ¬ Nonempty (S ≃* alternatingGroup (Fin 6))

variable {G : Type u} [Group G] [Finite G]

/-- The rank-two exclusion must also dispose of the genuine Sp₄(4) field case
using the source action and smaller-centralizer restrictions. -/
def RankTwoExclusion (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  HypothesisE61 KnownSimple.IsKnownSimple T M V → HypothesisE615 V →
    EarlierResults T M V →
    ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
      intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
        ∀ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel (Y ⧸ center Y) f → False

/-- The full eleven-sporadic C(5) list, including the genuine HS fixed-A₆ case. -/
def SporadicExclusion (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  HypothesisE61 KnownSimple.IsKnownSimple T M V → HypothesisE615 V →
    EarlierResults T M V →
    ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
      intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
        ChapterA.Section02.IsTheoremCSporadicModel (Y ⧸ center Y) → False

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
