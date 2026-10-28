module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.MarkedCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.Comparison

/-!
# The literal line-section Sylow in the SL₃ and Sp₄ branches

The marked point-core calculations identify R₁ with O₂(L₁)O₂(LT),
including the outer Sylow supplement. The first factor centralizes V₁
because L₁ does; the second already centralizes the whole chosen V.
This removes radical centralization from the line-action inputs in both
branches, with no block assumption and no splitting of the central kernel.

The section applications use the original kernel of conjugation on
L₁/O₂(L₁), intersected with C_G(V₁). The two-clause source consumers retain
Sylow-normalizer containment, owned by qt-d-1222-natural-line-action,
and the radical alternative, owned by qt-d-1222-natural-normalizer-source.
The G₂ branch is not asserted here.

Source: Aschbacher--Smith 11.1.5 and 11.2.3, pp.765--766,768--769.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual point-radical product discharges its line centralization. -/
theorem chosen_radical_centralizes_line_of_core_product
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    f.Ri 0 ≤ centralizer (f.Vi 0 : Set G) := by
  rw [hprod]
  exact sup_le ((pCoreIn_le _ _).trans (chosen_first_centralizes_line f))
    (D.core_centralizes.trans (centralizer_le (D.centralQuotientPreimage_le _)))

/-- The original SL₃ radical centralizes the original line. -/
theorem chosen_sl3_radical_centralizes_line
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) :
    f.Ri 0 ≤ centralizer (f.Vi 0 : Set G) :=
  chosen_radical_centralizes_line_of_core_product D S f
    (PointCohomology.PointGeometry.SL3Core.core_product D S m f)

/-- The original Sp₄ radical centralizes the full line preimage. -/
theorem chosen_sp4_radical_centralizes_line
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) :
    f.Ri 0 ≤ centralizer (f.Vi 0 : Set G) :=
  chosen_radical_centralizes_line_of_core_product D S f
    (PointCohomology.PointGeometry.Sp4Core.core_product D S m f)

/-- Both positive-branch inputs for the literal SL₃ line-section kernel. -/
theorem chosen_sl3_line_positive_steps
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 :=
  chosen_line_positive_steps_of_flag_geometry S f
    ((SylowNormalizer.invariantFlag_geometry D S f).2.2.model 0)
    (chosen_first_centralizes_line f) (chosen_sl3_radical_centralizes_line D S m f) hC

/-- Both positive-branch inputs for the literal Sp₄ line-section kernel. -/
theorem chosen_sp4_line_positive_steps
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 :=
  chosen_line_positive_steps_of_flag_geometry S f
    ((SylowNormalizer.invariantFlag_geometry D S f).2.2.model 0)
    (chosen_first_centralizes_line f) (chosen_sp4_radical_centralizes_line D S m f) hC

/-- The two original SL₃ conclusions now retain only the two source normalizer inputs. -/
theorem chosen_sl3_source_11_2_3_of_sylow_normalizer
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_radical_centralization D S f hX
    (chosen_sl3_radical_centralizes_line D S m f) hNT hradical

/-- The two original Sp₄ conclusions retain the same two source inputs. -/
theorem chosen_sp4_source_11_2_3_of_sylow_normalizer
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_radical_centralization D S f hX
    (chosen_sp4_radical_centralizes_line D S m f) hNT hradical
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
