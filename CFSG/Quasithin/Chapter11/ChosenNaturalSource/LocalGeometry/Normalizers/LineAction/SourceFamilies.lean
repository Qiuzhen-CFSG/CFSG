module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Sp4
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Final line-action assembly from the shared symplectic MS theorem

The SL₃ and G₂ Sylow-normalizer branches are complete. In the Sp₄ branch,
original escape constructs the literal C.1.31 input inside LT, with the
quotient marking induced by the original action. The shared intrinsic Sp₄
classification supplies shortness, and the completed displacement/movement
argument excludes the escape. The existing line-action and Frattini consumer
then gives both 11.2.3 clauses for every marked family.

The four literal inputs to the Frattini consumer are exported together, and
the two-clause theorem below applies them to the original flag and Cartan.
This completes the conditional line-action contract. The intrinsic
classification premise is owned by qt-c132-nonbinary-symplectic, and the
radical alternative by qt-d-1222-natural-normalizer-source. Under the
27 October conditional release, qt-d-1222-natural-local-geometry retains
their final discharge. No unconditional source theorem is asserted while
those earlier-source inputs remain explicit.
Source: Aschbacher--Smith C.1.31--32, pp.135--136; 3.3.16, p.591;
11.2.3, pp.768--769.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open ChapterC.RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ (T : Subgroup G))
local notation "R" => Subgroup.subgroupOf (T : Subgroup G) (L ⊔ (T : Subgroup G))

/-- Exact intrinsic C.1.31 data from symplectic Sylow-normalizer escape. -/
def sp4_escape_intrinsic_input
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Input K R S.field.degree S.field.Carrier := by
  let h := SylowNormalizer.sylow_msPair_of_escape D S (Coordinates.sp4 m) hescape
  exact Input.of_join h.nonbinary S.field.card_eq h.sqtk h.fitting h.component
    h.product h.radical h.characteristic m.groupEquiv

/-- The intrinsic marking is the original quotient action on every representative. -/
theorem sp4_escape_intrinsic_input_quotient_mk
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) (l : K) :
    (sp4_escape_intrinsic_input D S m hescape).quotientEquiv (QuotientGroup.mk' _ l) =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (subgroupOfEquivOfLe le_sup_left l)) := by
  change m.groupEquiv (subgroupOfCoreQuotientEquiv le_sup_left (QuotientGroup.mk' _ l)) = _
  rw [subgroupOfCoreQuotientEquiv_mk]

/-- Apply the shared intrinsic theorem to the actual escaping pair. -/
theorem sp4_sylow_normalizer_le_of_intrinsic_classification
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hclassification : Input K R S.field.degree S.field.Carrier → ChapterC.IsSp4FourBlock K) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hb := hclassification (sp4_escape_intrinsic_input D S m hescape)
  have hs : ChapterC.IsShort L := hb.1.of_mulEquiv (subgroupOfEquivOfLe le_sup_left)
  exact hescape (sp4_sylow_normalizer_le_of_short D S m hs)

/-- All marked-family Sylow-normalizer branches, with only the shared
intrinsic symplectic classification still explicit. -/
theorem sylow_normalizer_le_of_intrinsic_sp4_classification
    (c : Coordinates D S.field)
    (hclassification : Input K R S.field.degree S.field.Carrier → ChapterC.IsSp4FourBlock K) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  cases c with
  | sl3 m => exact sl3_sylow_normalizer_le D S m
  | sp4 m => exact sp4_sylow_normalizer_le_of_intrinsic_classification D S m hclassification
  | g2 m => exact SylowNormalizer.G2MS.g2_sylow_normalizer_le D S m

/-- The exact `hXU`, `hNT`, `hzero` and `hpositive` inputs of the original
Frattini consumer. The shared C.1.32 input is used only to exclude symplectic
Sylow-normalizer escape; the literal line-action and section-kernel assertions
come from the marked flag. Final discharge of the intrinsic input belongs to
qt-d-1222-natural-local-geometry. -/
theorem chosen_line_action_steps_of_intrinsic_sp4_classification
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hclassification : Input K R S.field.degree S.field.Carrier → ChapterC.IsSp4FourBlock K) :
    X ≤ normalizer (f.Vi 0 : Set G) ∧
    normalizer (T : Set G) ≤ normalizer (L : Set G) ∧
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) ≤
        normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G)) ∧
    (V ⊓ centralizer (L : Set G) ≠ ⊥ →
      centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
        ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
          (P : Subgroup (lineSectionKernel (f.Vi 0) (f.Li 0))).map
            (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0) := by
  refine ⟨SylowNormalizer.cartan_le_line_normalizer D S f hX,
    sylow_normalizer_le_of_intrinsic_sp4_classification D S c hclassification,
    chosen_line_normalized_of_marked_flag f hX, ?_⟩
  intro _ hC
  exact chosen_line_positive_steps D S f hC

/-- The original two-clause Frattini consumer, conditional only on the
identified shared symplectic theorem and the authorized radical alternative. -/
theorem chosen_source_11_2_3_of_intrinsic_sp4_classification
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hclassification : Input K R S.field.degree S.field.Carrier → ChapterC.IsSp4FourBlock K)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨hXU, hNT, hzero, hpositive⟩ :=
    chosen_line_action_steps_of_intrinsic_sp4_classification D S f hX hclassification
  exact chosen_source_11_2_3_of_action_steps D S f hX hXU hNT hzero hpositive hradical

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
