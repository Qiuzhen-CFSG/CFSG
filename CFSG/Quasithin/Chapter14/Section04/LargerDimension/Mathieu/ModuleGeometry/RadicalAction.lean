module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.ParabolicCoordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.MovedPlane
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.LineAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.Transvections

/-!
# Native radical calculations for the Mathieu branch

The marked F₄-point lies on an explicit projective line of vector dimension
two. The full second-actor image includes a nontrivial shear; its image on
this line is exactly the cubic rotation group, and its commutator with the
marked binary line has order four.

A concrete native involution acts as Frobenius on the actual parabolic
six-space. It fixes the marked line, inverts the central cubic scalar and
commutes with the full second image. Its fixed and moved spaces coincide
and have binary dimension three. A second native matrix acts as an
F₄-transvection with the marked F₄-point as its moved space.

Only precise group positions remain explicit: the complete second residual
image equals `secondImage`, `inverterUnit` lies in the literal point radical,
and `nativeTransvectionUnit` lies in its intersection with the genuine
triple-cover component. No operator, dimension, fixed-space or moved-space
conclusion is a premise. These positions belong to the actor-catalogue
assembly; quotient transport and the source E-containment bound belong to
the parent geometry assembly.

Source: Aschbacher–Smith 14.4.12, printed pp.1011–1012, and H.12.1,
printed pp.393–394. The native ATLAS provenance is retained in the imported
model; `RadicalAction/source/README.md` records the diagnostic positions.
-/

@[expose] public section

noncomputable section
open Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu M22TripleCover

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction

/-- The marked restricted line maps to the original marked binary line. -/
theorem markedLine_map_subtype :
    markedLine.map parabolicSpace.subtype = binaryLine markedVector := by
  rw [markedLine, Submodule.map_span, Set.image_singleton]
  rfl

/-- The full six-space image has a genuine two-part, although its image on
    the projective line is cyclic of order three. -/
theorem secondImage_has_involution :
    ∃ a ∈ secondImage, a ≠ 1 ∧ a * a = 1 := by
  refine ⟨modelUnits shear, ⟨shear, Subgroup.subset_closure (Or.inr rfl), rfl⟩, ?_, ?_⟩
  · intro he
    apply shear_ne_one
    apply Units.ext
    apply modelAction.injective
    have hh := congrArg (fun t : (Module.End (ZMod 2) parabolicSpace)ˣ => t.val) he
    exact hh.trans (map_one modelAction).symm
  · rw [← map_mul, shear_square, map_one]

/-- The two source moved-space bounds on the literal restricted quotient,
    with the order-four second commutator. The hypotheses specify only
    matrix/group positions, whose source identification has a separate owner. -/
theorem native_operator_calculations
    (A : Subgroup parabolic)
    (hA : A.map parabolicRepresentation.asGroupHom = secondImage)
    (hx : inverterUnit ∈ pointRadical.map actionGroup.subtype)
    (ht : nativeTransvectionUnit ∈
      (pointRadical ⊓ componentInclusion.range).map actionGroup.subtype) :
    Nat.card (subspaceCommutator parabolicRepresentation markedLine A) = 4 ∧
    subspaceCommutator parabolicRepresentation markedLine A ≤
      subspaceCommutator parabolicRepresentation ⊤ (pointRadical.subgroupOf parabolic) ∧
    (binaryPoint markedVector).comap parabolicSpace.subtype ≤
      subspaceCommutator parabolicRepresentation ⊤
        ((pointRadical ⊓ componentInclusion.range).subgroupOf parabolic) :=
  ⟨second_commutator_card A hA, second_moved_le_radical A hA hx,
    markedPoint_le_radical_component_moved ht⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
