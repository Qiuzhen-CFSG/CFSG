module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.MarkedField
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Application

/-!
# Degree-one coordinates on the original line action

Apply the marked field restriction to the whole-fixed-quotient coordinates
of the literal original first-summand image. The source marker and its
Thompson subgroup come from the same temporary-source construction.
The full earlier classifier remains the explicit input owned by the source
classification assembly.

Source: Aschbacher–Smith, proof of 15.3.67, printed pp.1153–1154,
using B.4.2(1), printed p.86 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.MarkedField.Application
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly ChapterB.SourceInduction
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
/-- The original whole fixed quotient is the natural SL₂ module over a field
of degree one, with its original actor and intertwining coordinates retained. -/
theorem original_degree_one_coordinates (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let σ := o.pairedRepresentation f hf hker
    ∃ F : ChapterB.QuasisimpleSource.BinaryField, F.degree = 1 ∧
      Nonempty (BestReduction.CentralQuotientCoordinates
        (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
        (ChapterB.QuasisimpleSource.linearNatural F 2)) := by
  let := o.module_normal
  let := o.module_elementary
  obtain ⟨F, ⟨c⟩⟩ := SourceClassification.Application.original_linearTwo_coordinates
    o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker classify
  exact ⟨F, temporary_field_degree_eq_one
    (SourceMarker.Application.temporarySource o hJ hNM hI hprod hNJ hG Z hZV hZ f hf hker)
    F c, ⟨c⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.MarkedField.Application
