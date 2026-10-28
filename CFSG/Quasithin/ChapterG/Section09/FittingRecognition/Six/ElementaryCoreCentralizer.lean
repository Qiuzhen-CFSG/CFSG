module
public import Theory.Representation.BinarySixElementaryTwentySevenCentralizer
public import CFSG.Quasithin.ChapterG.Section09.Setup

/-!
# The elementary degree-six core is self-centralizing

The faithful representation in the original Fitting hypothesis makes an
elementary three-core of order 27 self-centralizing. This discharges the
centralizer premise used to identify the generalized Fitting subgroup before
applying A.1.31(3).

Source: Aschbacher--Smith G.9.4, printed p.355.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The original Fitting hypothesis supplies the faithful binary action
needed for the self-centralizing elementary 27-core. -/
theorem elementary_threeCore_centralizer_le
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2) (hd : finrank (ZMod 2) V = 6)
    [IsElementaryAbelian 3 (pCore 3 G)] (hB : Nat.card (pCore 3 G) = 27) :
    centralizer (pCore 3 G : Set G) ≤ pCore 3 G :=
  Representation.BinarySixElementaryTwentySevenCentralizer.centralizer_le
    ρ h.faithful hd.le (pCore 3 G) hB

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
