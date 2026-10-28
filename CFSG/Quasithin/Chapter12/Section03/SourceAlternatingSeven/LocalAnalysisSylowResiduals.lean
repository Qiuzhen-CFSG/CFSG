module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsPreliminaries
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowReduction
public import Theory.GroupTheory.CComponent.AlternatingResidual

/-!
# Conditional A.3.18 assembly of the ambient Sylow-centre residuals

The fixed-point centralizer and its relative C-component follow from
uniqueness. For the fixed coset, C.2.7 component rigidity remains an
explicit input. With actual simple two-core quotients A₇ and A₆, the
centerless A.3.18 argument supplies both ambient residual identities.
Their embeddings are preserved in the application to `no_transport`.

This is a conditional assembly, not a constructor of `AmbientResiduals`
from the original setup. The two simple two-core quotient identifications
and `CosetComponents` must still be derived from the source hypotheses.
In particular the original central quotient models alone do not exclude
the triple covers.

Source: Aschbacher--Smith, A.3.18 and 3.3.22, printed pp.51--52 and 597.
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

/-- Uniqueness and the simple A₇ row give the fixed-point residual identity.
The actual two-core quotient is required; the given central quotient
alone does not remove the triple-cover possibility. -/
theorem fixed_residual_of_twoCore_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) : pointThreeResidual c = L := by
  let _ := S.hypothesis.quasisimple
  exact (P.fixed_component structural hc hne).map_primeToResidual_three_eq_of_quotient_alternating
    (P.fixed_component_le hc) (P.fixed_centralizer_le structural hc hne)
    (Or.inr rfl) eL (P.fixed_three_rank hc hne)

/-- Once the genuine C.2.7 component argument and the simple two-core
quotient are supplied, A.3.18 computes every residual in the fixed coset. -/
theorem six_residual_of_coset_components
    (C : P.CosetComponents)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    pointThreeResidual (c * (P.six : G)) = P.sixGroup := by
  let _ : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let _ : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  let _ := IsQuasisimple.of_mulEquiv e6.symm
  exact (C.component c hc).map_primeToResidual_three_eq_of_quotient_alternating
    (P.sixGroup_le_coset_centralizer hc) (C.normalizes c hc)
    (Or.inl rfl) e6 (P.coset_three_rank hc)

/-- Conditional assembly of the two literal identities. The two-core
models and coset C-components still have to be constructed from source. -/
theorem ambientResiduals_of_coset_components
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (C : P.CosetComponents) : P.AmbientResiduals :=
  ⟨fun _ hc => P.six_residual_of_coset_components C e6 hc,
    fun _ hc hne => P.fixed_residual_of_twoCore_quotient structural eL hc hne⟩

/-- Apply the residual calculation to the existing Sylow-normalizer
transport obstruction, with exactly its ambient maps. -/
theorem no_transport_of_coset_components
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M
    (P.ambientResiduals_of_coset_components structural eL e6 C)
    (S.hypothesis.source_sylow_normalizes structural) hg

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
