module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.CoveredKernel.PrimeDivisors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.CoveredKernel.Theta

/-!
# The covered centralizer kernel and original residual source

The original outside hypotheses give the {2,3} prime bound. The two
normalizer bounds exclude every cubic element of C_Y(V), so that kernel
is a two-group. Applying the existing source assembly now leaves only
the independently produced bound N_G(L₁) ≤ M. In particular neither
placement in L₁ nor the kernel conclusion is assumed.

Source: Aschbacher--Smith 13.3.7--9, printed pp.886--887; application to
13.8.12--16, pp.950--952.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SolvableExclusion.Residual
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
include d h

/-- The covered kernel assertion of 13.3.9; only the earlier L₁ normalizer
bound is retained beyond the original source hypotheses. -/
theorem covered_centralizer_kernel
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hN1 : normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M)
    {J Y : Subgroup G}
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (_hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hv : ∃v∈V₁, v∉V⊓centralizer (L:Set G) ∧ Y≤M⊓centralizer ({v}:Set G)) :
    IsPGroup 2 (Y⊓centralizer (V:Set G) : Subgroup G) := by
  obtain ⟨v,hv,hne,hfix⟩ := hv
  have h23 := covered_twoThree d h hJ hYJ hn v hv hne hfix
  exact isPGroup_two_of_isPiGroup_twoThree
    (h23.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left))
    (covered_kernel_no_cubic d h hc hN1 hJ hYJ hn v hv hne hfix)

/-- All literal 13.3.9 clauses, conditional only on the independently owned
13.2.2 bound for N_G(L₁). The covered kernel premise is discharged. -/
theorem source_of_one_normalizer
    (hN1 : normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M) :
    Source1339 L (one L (T:Subgroup G) V₁) (plus L (T:Subgroup G) V₁) T M V V₁ := by
  apply source_of_covered_kernel d h
  intro hc J Y hJ hYJ hp hn hv
  exact covered_centralizer_kernel d h hc hN1 hJ hYJ hp hn hv

end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
