module

public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets

/-!
# Actual coordinates and cosets for the hexacode point stabilizer

For an actor whose image contains the even hexacode group, the coordinate
homomorphism covers A₆. If its field point is the double-zero plane of a
coordinate pair, its literal stabilizer has the fifteen-pair coset action.
Coordinate relabeling preserves the alternating image.

These are the geometric inputs to the alternative-section repair of
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973). The full-weight
orbit exclusion and the intrinsic two-core lifts are separate obligations.
The hexacode geometry is proved in the narrowly imported model modules.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
open Atlas.Codes
open Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm pairHom first second)

variable {A : Type*} [Group A]

/-- The coordinate homomorphism of the actual embedded actor. -/
def coordinate (e : A →* HexAutomorphisms) : A →* Equiv.Perm (Fin 6) :=
  hexCoordinateSixHom.comp e

/-- The genuine stabilizer of a field point, viewed as a binary subspace. -/
noncomputable abbrev pointStabilizer (e : A →* HexAutomorphisms) (D : Submodule F hexacode) : Subgroup A :=
  (Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action
    (D.restrictScalars (ZMod 2))).comap e

/-- Covering the even hexacode group covers the alternating coordinate group. -/
theorem coordinate_coversAlternating (e : A →* HexAutomorphisms)
    (heven : hexSign.ker ≤ e.range) :
    ∀ g : alternatingGroup (Fin 6), ∃ a : A, coordinate e a = g.val := by
  intro g
  obtain ⟨h,hh⟩ := hexEvenCoordinate_surjective g
  obtain ⟨a,ha⟩ := heven h.property
  refine ⟨a, ?_⟩
  change hexCoordinateSixHom (e a) = g.val
  rw [ha]
  exact congrArg Subtype.val hh

/-- Coordinate relabeling preserves coverage of the alternating group. -/
theorem conjugate_coversAlternating (f : A →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a : A, f a = g.val)
    (r : Equiv.Perm (Fin 6)) :
    ∀ g : alternatingGroup (Fin 6), ∃ a : A,
      ((MulAut.conj r).toMonoidHom.comp f) a = g.val := by
  intro g
  have hg : r⁻¹ * g.val * r ∈ alternatingGroup (Fin 6) := by
    change Equiv.Perm.sign (r⁻¹ * g.val * r) = 1
    rw [map_mul, map_mul, map_inv, g.property, mul_one, inv_mul_cancel]
  obtain ⟨a,ha⟩ := hf ⟨r⁻¹ * g.val * r, hg⟩
  refine ⟨a, ?_⟩
  change r * f a * r⁻¹ = g.val
  rw [ha]
  group

/-- A double-zero point gives the actual fifteen-pair coset action. -/
noncomputable def cosetsOfZeroPair (e : A →* HexAutomorphisms)
    (heven : hexSign.ker ≤ e.range) (D : Submodule F hexacode)
    (s : Pair) (hs : D.restrictScalars (ZMod 2) = zeroPairPlane s) :
    (A ⧸ pointStabilizer e D) ≃ Pair :=
  BinaryPermutation.SixPairsQuadratic.pairCosets (coordinate e)
    (coordinate_coversAlternating e heven) (pointStabilizer e D) s (by
      intro a
      change e a ∈ Representation.BinaryOffender.subspaceStabilizer
        Representation.Hexacode.action (D.restrictScalars (ZMod 2)) ↔ _
      rw [hs]
      exact zeroPairPlane_stabilizer_iff (e a) s)

/-- Equivariance retains the original actor and its literal point stabilizer. -/
theorem cosetsOfZeroPair_equivariant (e : A →* HexAutomorphisms)
    (heven : hexSign.ker ≤ e.range) (D : Submodule F hexacode)
    (s : Pair) (hs : D.restrictScalars (ZMod 2) = zeroPairPlane s)
    (a : A) (q : A ⧸ pointStabilizer e D) :
    cosetsOfZeroPair e heven D s hs (a • q) =
      pairPerm (coordinate e a) (cosetsOfZeroPair e heven D s hs q) :=
  BinaryPermutation.SixPairsQuadratic.pairCosets_equivariant _ _ _ _ _ a q

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
