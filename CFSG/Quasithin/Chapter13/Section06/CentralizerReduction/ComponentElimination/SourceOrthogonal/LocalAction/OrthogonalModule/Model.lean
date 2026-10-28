module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Action
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight.PermutationComparison

/-!
# Orthogonal coordinates on the literal moved section

Compose the selected natural-section coordinates with the explicit deleted
module comparison. The result identifies U_K/C_{U_K}(K) with the split
quadratic six-space and intertwines the entire plus action with its marked
S₈ orthogonal action. The source FF argument must still construct the
NaturalMovedSection input; dimension six is a consequence of its genuine
coordinates, not a recognition premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph following 13.6.23, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection Representation.BinaryLinearRecognition
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Rotate the coordinates and actor together while retaining the literal
upper and central subrepresentations. This uses the same permutation as the
original-seed marking. -/
noncomputable def NaturalMovedSection.conjugate
    (d : NaturalMovedSection K L T z v hL hz) (r : Equiv.Perm (Fin 8)) :
    NaturalMovedSection K L T z v hL hz where
  actor := d.actor.trans (MulAut.conj r)
  component_image := by
    change (plusImage K L T z v hL hz K).map
      ((MulAut.conj r).toMonoidHom.comp d.actor.toMonoidHom) = _
    rw [← Subgroup.map_map, d.component_image]
    exact mem_normalizer_iff_map_conj_eq.mp (by
      rw [Subgroup.normalizer_eq_top]
      exact mem_top r)
  upper := d.upper
  upper_mem := d.upper_mem
  central := d.central
  central_mem := d.central_mem
  coordinates := d.coordinates.trans (LinearEquiv.ofBijective
    (BinaryPermutation.naturalRepresentation (Fin 8) r)
    ((BinaryPermutation.naturalRepresentation (Fin 8)).apply_bijective r))
  equivariant := by
    intro g w
    change BinaryPermutation.naturalRepresentation (Fin 8) r
      (d.coordinates (d.central.quotientRepresentation g w)) = _
    rw [d.equivariant]
    change _ = BinaryPermutation.naturalRepresentation (Fin 8) (r * d.actor g * r⁻¹)
      (BinaryPermutation.naturalRepresentation (Fin 8) r (d.coordinates w))
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group

/-- One chosen identification of the actual moved section with orthogonal six-space. -/
noncomputable def NaturalMovedSection.orthogonalCoordinates
    (d : NaturalMovedSection K L T z v hL hz) :
    (d.upper.toSubmodule ⧸ d.central.toSubmodule) ≃ₗ[ZMod 2]
      ClassicalOrthogonal.VectorD 3 (ZMod 2) :=
  d.coordinates.trans naturalEightOrthogonalEquiv

/-- The chosen coordinates intertwine the whole literal plus action. -/
theorem NaturalMovedSection.orthogonal_equivariant
    (d : NaturalMovedSection K L T z v hL hz)
    (g : Gplus K L T z v hL hz) (w : d.upper.toSubmodule ⧸ d.central.toSubmodule) :
    d.orthogonalCoordinates K L T z v hL hz (d.central.quotientRepresentation g w) =
      (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
        (d.orthogonalCoordinates K L T z v hL hz w) := by
  change naturalEightOrthogonalEquiv (d.coordinates (d.central.quotientRepresentation g w)) = _
  rw [d.equivariant]
  exact naturalEightOrthogonalEquiv_permutation (d.actor g) (d.coordinates w)

/-- The dimension assertion follows from the actual action identification. -/
theorem NaturalMovedSection.section_finrank (d : NaturalMovedSection K L T z v hL hz) :
    Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 :=
  (d.orthogonalCoordinates K L T z v hL hz).finrank_eq.trans finrank_orthogonalEight

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
