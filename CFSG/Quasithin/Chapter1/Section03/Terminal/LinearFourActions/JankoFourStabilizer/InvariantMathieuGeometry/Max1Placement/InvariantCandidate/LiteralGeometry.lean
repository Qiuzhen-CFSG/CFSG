module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.CenterBounds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Counting
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces

/-!
# Intrinsic core recovery from octad binary geometry

Common-octad placement identifies each local L₄(2) section with the
solvable residual R of an octad preimage. Suppose Z(O₂(R)) lies in the
intrinsic elementary kernel V of order 2048 and its centralizer lies in
Q, the preimage of the octad stabilizer's two-core of order at most 16.
Then V centralizes Z(O₂(R)).

For an abelian subgroup E of order 2048 in that centralizer, an element
outside V bounds |E ∩ V| by 128. Counting forces the image of E to fill
O₂(P). Hence E ∩ V centralizes all of Q, whose fixed-space order is
strictly less than 128, a contradiction. Thus E ≤ V, and orders give
E = V. This uses the actual extension without choosing a splitting.

The theorem `literalIntrinsicCoreRecovery_of_bounds` isolates the three
binary-model bounds. The final theorem `literalIntrinsicCoreRecovery`
supplies them from `CenterBounds` and `FixedSpaces`, leaving only the
common-octad placement hypothesis for the parent assembly.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the local
configuration used in 1.3.9, p.514; GLS3 Table 5.3i.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels Sporadic.Mathieu.M24LocalGeometry
attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- The binary fixed-space bounds exclude an elementary subgroup outside the intrinsic core. -/
theorem literalCoreRecovery_of_octad_bounds (O : Octad)
    (hcenter : coreCenter (literalOctadResidual O) ≤ pCore 2 certifiedMathieuSubgroup)
    (hcentralizer : centralizer (coreCenter (literalOctadResidual O) : Set certifiedMathieuSubgroup) ≤
      literalOctadTwoPreimage O)
    (hfixed : ∀ x ∈ literalOctadTwoPreimage O, x ∉ pCore 2 certifiedMathieuSubgroup →
      Nat.card ((centralizer ({x} : Set certifiedMathieuSubgroup)).subgroupOf
        (pCore 2 certifiedMathieuSubgroup)) ≤ 128)
    (hall : Nat.card ((centralizer (literalOctadTwoPreimage O : Set certifiedMathieuSubgroup)).subgroupOf
      (pCore 2 certifiedMathieuSubgroup)) < 128) :
    CoreRecoveryInside (literalOctadResidual O) := by
  let := literalCore_elementary
  constructor
  · intro x hx z hz
    exact congrArg Subtype.val (mul_comm (⟨z, hcenter hz⟩ : pCore 2 certifiedMathieuSubgroup)
      ⟨x, hx⟩)
  · intro E hE
    let := hE.2.1
    have hkcomm : IsMulCommutative literalMathieuMap.ker := by
      rw [literalMathieuMap_ker]
      infer_instance
    let := hkcomm
    have hfixed' : ∀ x ∈ ((octadStabilizer O).pCoreIn 2).comap literalMathieuMap,
        x ∉ literalMathieuMap.ker →
        Nat.card ((centralizer ({x} : Set certifiedMathieuSubgroup)).subgroupOf
          literalMathieuMap.ker) ≤ 128 := by
      rw [literalMathieuMap_ker]
      exact hfixed
    have hall' : Nat.card ((centralizer
        (((octadStabilizer O).pCoreIn 2).comap literalMathieuMap : Set certifiedMathieuSubgroup)).subgroupOf
        literalMathieuMap.ker) < 128 := by
      rw [literalMathieuMap_ker]
      exact hall
    have hle := abelian_le_kernel_of_centralizer_bounds literalMathieuMap
      ((octadStabilizer O).pCoreIn 2) 128 16 (by decide)
      (literalOctadCore_card_le O) hfixed' hall' E (hE.1.trans hcentralizer)
      (by rw [hE.2.2])
    rw [literalMathieuMap_ker] at hle
    exact eq_of_le_of_card_ge hle (by rw [literalCore_card, hE.2.2])

/-- Common-octad placement and the explicit binary geometry imply literal
intrinsic recovery. -/
theorem literalIntrinsicCoreRecovery_of_bounds
    (hOctad : MathieuLocalSections.OctadPlacement)
    (hcenter : LiteralOctadCenterBounds)
    (hfixed : LiteralOctadElementFixedBound)
    (hall : LiteralOctadCommonFixedBound) : LiteralIntrinsicCoreRecovery := by
  intro B T hB hlocal
  obtain ⟨O, him, hle⟩ := literalImage_eq_octad hOctad B T hB hlocal
  rw [literalLocal_eq_residual B T O hlocal him hle]
  exact literalCoreRecovery_of_octad_bounds O (hcenter O).1 (hcenter O).2
    (hfixed O) (hall O)

/-- Common-octad placement recovers the intrinsic two-core of the certified
max1 subgroup from the center of any source-local L₄(2) section's two-core. -/
theorem literalIntrinsicCoreRecovery (hOctad : MathieuLocalSections.OctadPlacement) :
    LiteralIntrinsicCoreRecovery :=
  literalIntrinsicCoreRecovery_of_bounds hOctad
    (literalOctad_centerBounds literalOctad_elementFixedBound)
    literalOctad_elementFixedBound literalOctad_commonFixedBound

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
