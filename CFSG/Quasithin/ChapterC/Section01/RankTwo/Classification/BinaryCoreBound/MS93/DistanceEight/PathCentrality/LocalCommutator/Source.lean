module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic

/-!
# The two source branches of MS93 (4.4.1)

The source's c(W/Z_c) = 1 means a split natural section with its literal
quotient and conjugation action, not merely a count of constituents. We use
the existing expanded NaturalSectionAt interface. Basic proves that Z_c
belongs to W for the distance-two pairs considered here.

LocalControlAt records exactly the two conclusions already published in
LocalCommutatorControl. No constructor is asserted here. The two remaining
arguments are the natural-section case on pp.890--891 and the contradiction
from failure of that section on pp.891--892. Their final assembly must retain
only LocalSource, Geometry, CommonFacts and b > 4 as premises.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), pp.890--892; expanded c notation on p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The two conclusions of (4.4.1) at the specified ordered distance-two pair. -/
def LocalControlAt (a c : Vertex R) : Prop :=
  ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c ∧
    ∀ x ∈ Q R c, ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c →
      Z R c ≤ ⁅zpowers x, localZSpan R a c⁆ ⊔ fixedCore R c

/-- The full expanded c(W/Z_c) = 1 condition at the actual local stabilizer.
Existence of the quotient marking is part of the condition. -/
def HasNaturalSection (a c : Vertex R) : Prop :=
  Nonempty (Escape.NaturalSectionAt c (localZSpan R a c) (Z R c))

/-- Match the pointwise conclusions with the existing public contract. This
is only an interface equivalence, not a constructor from source hypotheses. -/
theorem localCommutatorControl_iff : LocalCommutatorControl R ↔
    ∀ a c, color R a = false → color R c = false → (cosetGraph R).dist a c = 2 →
      ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c → LocalControlAt R a c := Iff.rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator
