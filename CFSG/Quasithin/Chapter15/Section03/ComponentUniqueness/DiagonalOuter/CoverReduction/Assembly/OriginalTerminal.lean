module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.MixedCentralizerSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FieldAmbientSource

/-!
# The original field-centralizer contradiction

The selected mixed centralizer and field-coset calculations discharge every remaining premise of the field terminal. The actual marked reduction is retained throughout.
Source: Aschbacher–Smith, 15.3.35–38, printed pp.1135–1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- The field-centralizer contradiction on the original marked reduction. -/
theorem Reduction.false_of_original (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (R : Reduction d I L) (h : Setup d I L) : False := by
  obtain ⟨⟨eO⟩, P, hP, hc, he⟩ := source_mixed_centralizer s h R.coverData R.sylow
  let : IsExtraspecial 3 P := hP
  exact R.field_exclusion_of_original hG s h
    (source_field_coset_conjugate s h R.coverData R.sylow) eO P hc
    (fun x => (congrArg (fun k : ℕ => x ^ k) he).symm.trans
      (Monoid.pow_exponent_eq_one x))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
