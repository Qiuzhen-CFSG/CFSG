module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.InputBridge
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.BasisData

/-!
# The published basis and literal left-generator targets

Kernel checks identify the shared basis words exactly. Packed copies of the
small index tables then check LEFT multiplication, with A and B in their
published order, on every point of the natural action.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

open Inputs CertificateData

theorem basis_blocks : ∀ b : Fin 3, (basisIndices[b.val]!).toList =
    unpack 13 (min 128 (300-b.val*128)) (basisBlock b.val) := by
  decide +kernel

theorem basisCode_eq (j : Fin 300) : basisCode j.val = tableEntry basisIndices j.val := by
  exact (packed_lookup basisIndices basisBlock 13 3 300 (by decide) basis_blocks j).symm

theorem left_blocks : ∀ s : Fin 2, (leftIndices[s.val]!).toList =
    unpack 13 300 (leftBlock s.val) := by
  decide +kernel

theorem leftCode_eq (s : Fin 2) (j : Fin 300) :
    leftCode s.val j.val = (leftIndices[s.val]!)[j.val]! := by
  rw [← Array.getElem!_toList, left_blocks s, unpack_get _ _ _ _ j.isLt]
  rfl

theorem basis_words : ∀ j : Fin 300, indexWord (basisIndex j) = basisWord j := by
  decide +kernel

private theorem left_points_packed : ∀ (s : Fin 2) (j : Fin 300) (x : Fin 11),
    digit (permCode ((leftCode s.val j.val) % 7920)) x.val =
      digit (genCode s.val) (digit (permCode ((basisCode j.val) % 7920)) x.val) := by
  decide +kernel

theorem left_points (s : Fin 2) (j : Fin 300) (x : Fin 11) :
    digit (permCode (leftIndex s j).val) x.val =
      digit (genCode s.val) (digit (permCode (basisIndex j).val) x.val) := by
  simpa only [leftIndex, basisIndex, Fin.val_ofNat, ← leftCode_eq s j, ← basisCode_eq j]
    using left_points_packed s j x

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
