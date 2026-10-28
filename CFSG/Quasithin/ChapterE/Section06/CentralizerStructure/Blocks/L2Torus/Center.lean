module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Diagonal
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Nonvanishing
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.CoverLift
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.GlobalFixed

/-!
# The intrinsic L₂-block center calculation

For a marked natural block and an independent diagonal section, the Sylow
omega-center is the direct product of its global central part and its torus
displacement. Odd-orbit averaging identifies the torus-fixed part with the
global central part, completing the coprime splitting.

The explicit earlier-source input `CoverLift.RankOneCoverTheorem` retains the
orthogonal universal cover and the full rank-one assertion of I.2.3(3).
Applying it to the constructed cover on U(L) fixes the root-line preimage
under S. This supplies a nonzero displacement, whose injective natural
coordinate is then surjective. Its order is 2ⁿ and literal torus conjugation
is regular on its nonidentity elements, with natural-line weight u.

`center_calculation_of_I23` assembles all four conclusions. The diagonal
section and I.2.3 remain explicit inputs for the parent source-theorem owner;
no center, order or regularity conclusion is assumed, and C.1.13 is not used.

Source: Aschbacher–Smith, E.6.7, printed p.246; C.1.12, p.124; I.2.3, p.413.
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterE.Section06.L2Torus

universe u v
variable {L : Type u} {F : Type v} [Group L] [Finite L] [Field F] [Finite F]
    [CharP F 2] {B : Subgroup L} {a : MarkedBlockModel L B F}

/-- The Sylow omega-center splits over its global central part. This step
uses odd-orbit averaging and coprime action, with no covering hypothesis. -/
theorem DiagonalSection.omegaCenter_decomposition (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) =
      (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ center L) ⊔
        ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ := by
  simpa only [d.omegaCenter_fixed_eq_center hn hF hshort S hS] using
    d.omegaCenter_coprime_decomposition S hS hn hF

/-- Applying I.2.3 to the actual cover discharges the fixed-root-line premise
in the order calculation. No nonvanishing or cardinality premise remains. -/
theorem DiagonalSection.displacement_card_of_I23 (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hI23 : CoverLift.RankOneCoverTheorem.{v, u} F n) :
    Nat.card ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ = 2 ^ n :=
  d.displacement_card_of_rootLine_fixed hshort S hS hn hF
    (CoverLift.rootLine_le_centralizer_of_I23 hshort a hn hF hI23 S hS)

/-- The complete intrinsic center calculation used by the L₂-block branch
of E.6.7, conditional on the explicit earlier-source covering theorem I.2.3. -/
theorem DiagonalSection.center_calculation_of_I23 (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hI23 : CoverLift.RankOneCoverTheorem.{v, u} F n) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Z = (Z ⊓ center L) ⊔ ⁅Z, d.torus⁆ ∧
      Disjoint (Z ⊓ center L) ⁅Z, d.torus⁆ ∧
      Nat.card ↥⁅Z, d.torus⁆ = 2 ^ n ∧
      RegularConjugationOnNonidentity d.torus ⁅Z, d.torus⁆ :=
  ⟨d.omegaCenter_decomposition hshort S hS hn hF,
    d.omegaCenter_center_disjoint S hS hn hF,
    d.displacement_card_of_I23 hshort S hS hn hF hI23,
    d.regular_displacement hshort S hS hn hF⟩

end CFSG.Quasithin.ChapterE.Section06.L2Torus
