module

public import CFSG.Quasithin.ChapterH.Section13To16.ModuleDuality
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint

/-!
# The avoidance step in H.15.7

The six-point map, when proved bijective, gives both source bounds for
arbitrary cocode subspaces. The M₂₃ bound uses pairs containing the native
point zero. These endpoints retain the map-bijectivity premise explicitly;
they do not assert the complete source theorem or the normalizer structure.

Source: Aschbacher–Smith, H.15.7(3), printed pp.401–402, combined manuscript
of 1 March 2004. The owning assembly must discharge the fixed-point model.
-/

public section

open Sporadic.Mathieu MathieuCode MathieuCode.SixPoint
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The M₂₄ avoidance conclusion, conditional on the canonical six-point model. -/
theorem cocode_pairAvoidance_of_sixPointMap (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6) (hmap : Function.Bijective (toFixedCocode D))
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation D)
    (havoid : Disjoint (I : Set Cocode) cocodeO2) : Module.finrank (ZMod 2) I ≤ 2 :=
  finrank_le_two_of_bijective_fixedPoint_map D hD hmap I hI havoid

/-- The M₂₃ avoidance conclusion for a subgroup fixing the native point zero. -/
theorem m23_cocode_pairAvoidance_of_sixPointMap (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6) (hmap : Function.Bijective (toFixedCocode D))
    (h0 : (0 : Fin 24) ∈ MulAction.fixedPoints D (Fin 24))
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation D)
    (havoid : Disjoint (I : Set Cocode) m23CocodeO2) : Module.finrank (ZMod 2) I ≤ 4 := by
  have hd := (LinearEquiv.ofBijective (toFixedCocode D) hmap).finrank_eq
  rw [finrank_fixedPoint_core D hD] at hd
  exact finrank_le_four_of_fixed_finrank D hD h0 hd.symm I hI havoid

end CFSG.Quasithin.ChapterH.Section13To16
