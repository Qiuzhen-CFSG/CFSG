module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PairedClosure
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleComponentAction

/-!
# The genuine solvable outside source

The original quotient alternatives are the single S3 and paired wreath
rows. The completed single-component action proof handles the first row;
the actual paired-point argument and Borel quotient contradiction handle
the second. The same original Context supplies normalization and Baumann
control, so no classification, module or point-exclusion callback remains.
Source: Aschbacher--Smith 13.2.7--14, pp.880--884.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Every original solvable outside subgroup centralizes the full Sylow
omega-center, with no remaining local source premise. -/
theorem original_solvable_centralizes_omega_from_source
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  have hB := baumann_normalizer_of_many d hmany
  rcases source_residual_core_quotient_models d hH hB hZ hs with ⟨he,_⟩ | ⟨he,_⟩
  · obtain ⟨e⟩ := he
    obtain ⟨e₃⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    exact hZ (single_outside_centralizes_omega d hH hB ⟨e.trans e₃⟩)
  · exact hZ (paired_outside_centralizes_omega d hmany hH hs he)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
