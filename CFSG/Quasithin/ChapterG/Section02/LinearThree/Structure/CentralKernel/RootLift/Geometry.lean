module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift.GeometryInterface
public import Theory.SpecificGroups.SL3.PointRadicalSylow

/-!+# The finite SL₃ root calculation for G.2.5

Displacement in the marked, pointwise fixed subspace makes every element of
the marked radical square to one. After aligning the specified Sylow with
UT₃, its order identifies one of the two root planes. The coordinate-swap
construction supplies the complementary intersection with a literal right
conjugate. This works over every finite field of order 2ⁿ, including n = 1.

This discharges exactly `ModelRootGeometry`, the independent matrix premise
of `RootLift.hasRootLift_of_model_geometry`. The central-extension assembly
remains in `RootLift`; importing only its interface avoids a cycle.
Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, and G.2.3(3).
-/

public section
open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel

/-- The marked Sylow contains the required complementary root, with every
matrix premise of the root-lift interface discharged. -/
theorem modelRootGeometry (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : ModelRootGeometry F := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro point A R _hdim hcard hmove hfix hAR _hnormalizer
  apply SpecialLinearGroup.PointRadicalSylow.exists_root_complement F hn hF A R hAR hcard
  intro a ha
  exact SpecialLinearGroup.PointRadicalSylow.square_eq_one_of_point_action F point a
    (hmove a ha) (hfix a ha)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
