module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3.Seed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.ChiefSection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Orbit

/-!
# Applying the literal SL₃ action to the exceptional GO argument

The proved natural-coordinate calculations discharge the first residual's
rank-one model, fixed-line and full-commutator premises in the component
and seven-residual consumers. Actual shortness also supplies V=V_M.

The central core section's commutator bound, order and fixed-free-five
subgroup remain explicit. Their proof, the Sp₄ action, centralizer control,
and final assembly remain with qt-d-1222-natural-point-fixed-summand;
qt-d-1222-natural-normalizer-source is the enclosing source assembly owner.
This module does not assert completion of 11.1.5.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The component-normality consumer now has no residual model or fixed-line premise. -/
theorem normalizes_first (f : InvariantFlag (Coordinates.sl3 m))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Li 0 : Set G) :=
  radical_normalizer_normalizes_first D S f (first_isPSL D S m f)
    (first_centralizes_line D S m f) hcenter hne

/-- Trivial action on the literal central core section preserves the original
SL₃ seed: the natural calculation discharges [V,L₁]=V. -/
theorem section_kernel_normalizes_seed (f : InvariantFlag (Coordinates.sl3 m))
    (y : normalizer (f.Li 0 : Set G))
    (hy : y ∈ (ChiefSection.normalizerAction (f.Li 0)).ker) :
    (y : G) ∈ normalizer (V : Set G) :=
  ChiefSection.normalizes_of_section_kernel (f.Li 0) (seed_le_first_core D S m f)
    (seed_commutator D S m f) y hy

/-- Application of the literal section calculation to the original seven-residual.
Only the section commutator, order and fixed-free-five inputs remain. -/
theorem sevenResidual_normalizes_seed_of_sections
    (f : InvariantFlag (Coordinates.sl3 m)) (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (hcard : Nat.card (CoreCentralSection (f.Li 0)) = 256)
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥) :
    (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype ≤ normalizer (V : Set G) :=
  chosen_exceptional_sevenResidual_normalizes_seed_of_sections D S f
    (first_isPSL D S m f) (first_centralizes_line D S m f) X hcenter hfixed he
    hc hcard B hB hBcard hBfixed (seed_commutator D S m f)

/-- The original SL₃ escape contradiction, with the natural-coordinate
premises proved and shortness supplying V=V_M. The remaining section inputs
and their discharge belong to this fixed-summand task. -/
theorem exceptional_escape_of_short_sections
    (f : InvariantFlag (Coordinates.sl3 m)) (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (hcard : Nat.card (CoreCentralSection (f.Li 0)) = 256)
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥) : False :=
  chosen_exceptional_escape_of_sections D S f (first_isPSL D S m f)
    (first_centralizes_line D S m f) X hescape
    (PointBlocks.seed_eq_conjugateSpan_of_short D hb) hcenter h hfixed he
    hc hcard B hB hBcard hBfixed (seed_commutator D S m f)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
