module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResiduals
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsPreliminaries

/-!
# LocalAnalysisSylowResiduals at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResiduals`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem fixed_residual_of_twoCore_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) : pointThreeResidual c = L := by
  let _ := S.hypothesis.quasisimple
  exact (P.fixed_component_at structural hc hne).map_primeToResidual_three_eq_of_quotient_alternating
    (P.fixed_component_le hc) (P.fixed_centralizer_le_at structural hc hne)
    (Or.inr rfl) eL (P.fixed_three_rank hc hne)

theorem ambientResiduals_of_coset_components_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (C : P.CosetComponents) : P.AmbientResiduals :=
  ⟨fun _ hc => P.six_residual_of_coset_components C e6 hc,
    fun _ hc hne => P.fixed_residual_of_twoCore_quotient_at structural eL hc hne⟩

theorem no_transport_of_coset_components_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M
    (P.ambientResiduals_of_coset_components_at structural eL e6 C)
    (S.hypothesis.source_sylow_normalizes_at structural) hg

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

