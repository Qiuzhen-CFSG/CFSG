module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Assembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceAssembly.Local

/-!
# Classification and identification on the literal source action

The original local hypotheses construct the marker and the temporary source.
The source Z-normalizer condition then excludes the SL₃ and S₅ alternatives
without requiring whole central-quotient coordinates. The full earlier SL₂
row then supplies those coordinates on precisely the action used by
`original_conclusions_of_local`.

The marked Thompson/Sylow comparison then constructs the full unreduced witness
and discharges that parameter of the existing original-action consumer. It
returns the S₃ image, exact section kernel, moved dimensions and index-three
intersection for the original I₀ and full I actions. The canonical variant also
constructs the faithful centralizer quotient. The universal adequate earlier
classifier remains explicit and belongs to the general B.5 classification owner.

Source: Aschbacher–Smith, proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.Application
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly OriginalComparison ChapterB.SourceInduction
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {K : GroupClass.{u}} {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
  (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
  (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G))
  (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M)
  (hG : IsSQTK K (lineNormalizer E))
  (Z : Subgroup G) (hZV : Z ≤ V)
  (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- The same original first-summand image has a genuine natural SL₂ section,
retaining the original quotient and both possible nonsplit extensions. -/
theorem original_linearTwo_section (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let σ := o.pairedRepresentation f hf hker
    Nonempty (LinearTwoSection
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype))) := by
  let := o.module_normal
  let := o.module_elementary
  exact temporary_linearTwo_section
    (SourceMarker.Application.temporarySource o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker)
    classify

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- The original literal first-summand image has natural SL₂ coordinates on
its whole fixed quotient. This discharges the module-coordinate gap, retaining
the positive field degree until the marked-normalizer comparison. -/
theorem original_linearTwo_coordinates (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let σ := o.pairedRepresentation f hf hker
    ∃ F : ChapterB.QuasisimpleSource.BinaryField,
      Nonempty (BestReduction.CentralQuotientCoordinates
        (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
        (ChapterB.QuasisimpleSource.linearNatural F 2)) := by
  let := o.module_normal
  let := o.module_elementary
  exact temporary_linearTwo_coordinates
    (SourceMarker.Application.temporarySource o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker)
    classify

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- The literal original action supplies the whole-quotient and marked Borel
witness required by `SourceAssembly.original_conclusions_of_local`. -/
theorem original_unreduced_alternative (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let σ := o.pairedRepresentation f hf hker
    Nonempty (BestReduction.UnreducedAlternative
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E))) := by
  let := o.module_normal
  let := o.module_elementary
  exact temporary_unreduced_alternative
    (SourceMarker.Application.temporarySource o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker)
    classify

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- Apply the existing original-I₀ and full-I comparison with every local
marker and classification witness discharged. Only the universal earlier
classifier remains beyond the preceding source hypotheses. -/
theorem original_conclusions_of_classification (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
    let σ := o.pairedRepresentation f hf hker
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (originalRepresentation σ) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker (originalRepresentation σ)) = 2 ∧
    (originalRepresentation σ).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (originalActor T V E) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker
      (FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker))) = 2 ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let := o.module_normal
  let := o.module_elementary
  let := Descent.sectionKernel_normal V E o.line_le
  obtain ⟨a⟩ := original_unreduced_alternative
    o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker classify
  exact SourceAssembly.original_conclusions_of_local
    o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker classify a

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- Construct the faithful quotient and discharge its unreduced witness.
The original action image, kernel, moved dimensions and intersection index
now follow from the local inputs and the universal earlier classifier alone. -/
theorem canonical_original_conclusions_of_classification
    (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
    let C := centralizer
      (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
    let f := QuotientGroup.mk' C
    let hf := QuotientGroup.mk'_surjective C
    let hker := QuotientGroup.ker_mk' C
    let σ := o.pairedRepresentation f hf hker
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (originalRepresentation σ) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker (originalRepresentation σ)) = 2 ∧
    (originalRepresentation σ).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (originalActor T V E) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker
      (FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker))) = 2 ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let := o.module_normal
  let := o.module_elementary
  let := Descent.sectionKernel_normal V E o.line_le
  let C := centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
  exact original_conclusions_of_classification o hJ hNM hI hprod hNJ hG Z hZV hZ
    (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) classify

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.Application
