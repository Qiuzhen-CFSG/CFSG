module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSourceResidual
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwo
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowNormalizer

/-!
# Intrinsic weight-six inputs and the A₆ rigidity branch

The cover-compatible quotient recognition and common two-core calculation
construct every local `Models` field and the literal section-Sylow input.
Relative normality in C_G(e) then makes the residual a C-component, so
normality alone supplies the remaining input to the Frattini--theta proof.

When the residual's two-core quotient is A₆, the existing genuine C.2.7
star-model exclusions establish this normality. Component orbits give the
bound for every weight-six vector. The actual LocalAnalysis application
also discharges its earlier Sylow-normalizer premise.

The triple-cover rigidity branch and both weight-two inputs remain with
qt-d-1236-1238-point-centralizers; final source assembly remains with
qt-d-1231-local-analysis. The last constructor is conditional on those
weight-two inputs and the A₆ branch, and is not full 12.3.6--8.
Source: Aschbacher--Smith 12.3.6--8, printed pp.809--810.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points
variable (P : Points E)

/-- Construct all literal local models without the contrary-normalizer premise. -/
def sourceModels
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : P.Models :=
  P.models_of_quotients P.fiveCoreEquiv
    (E.sixResidualCentralEquiv P.six P.six_weight) (P.six_core_eq_core structural)

/-- The original section centralizer has O₂(LT) as an embedded Sylow subgroup. -/
theorem six_source_section_sylow
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ R : Sylow 2 (PointCentralizers.Y (L := L) P.six),
      (R : Subgroup _).map (PointCentralizers.Y (L := L) P.six).subtype =
        PointCentralizers.Q T L :=
  P.six_section_sylow_of_core_eq (P.six_core_eq_core structural)

end SylowNormalizer.Points
namespace PointCentralizers

/-- Intrinsic recognition discharges every weight-six input except relative normality. -/
theorem sixInput_of_normalizes (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : H P.six ≤ normalizer (P.sixGroup : Set G)) : SixInput P := by
  have hKC : P.sixGroup ≤ H P.six :=
    (SylowNormalizer.pointResidual_le L (P.six : G)).trans inf_le_right
  let A := P.sixGroup.subgroupOf (H P.six)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let e : A ≃* P.sixGroup := subgroupOfEquivOfLe hKC
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup) :=
    E.sixResidualCore_quasisimple P.six P.six_weight
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp : IsPPerfect 2 A := by
    intro N hN hQ
    let := hN
    let := hQ.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  exact ⟨hn,isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : A.Normal).isSubnormal hp,
    inferInstance,⟨E.sixResidualCentralEquiv P.six P.six_weight⟩,
    P.six_source_section_sylow structural⟩

/-- The source Frattini--theta argument now needs only residual normality. -/
theorem six_centralizer_le_of_normalizes (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : H P.six ≤ normalizer (P.sixGroup : Set G)) :
    H P.six ≤ normalizer (L : Set G) :=
  six_centralizer_le P (sixInput_of_normalizes P structural hn) structural

/-- C.2.7 excludes every proper enlargement in the A₆ two-core-quotient branch. -/
theorem sixInput_of_simple_core (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    SixInput P := by
  apply sixInput_of_normalizes P structural
  simpa only [one_mul] using
    (P.cosetComponents_of_source structural (P.sourceModels structural) e6).normalizes
      1 P.fixed.one_mem

/-- The A₆ branch controls the ambient centralizer of every weight-six vector. -/
theorem six_centralizers_of_simple_core (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  E.centralizer_le_of_same_weight v P.six (hv.trans P.six_weight.symm)
    (six_centralizer_le P (sixInput_of_simple_core P structural e6) structural)

/-- The only remaining weight-six rigidity branch has the concrete triple-cover quotient. -/
theorem six_centralizer_le_or_triple (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    H P.six ≤ normalizer (L : Set G) ∨
      Nonempty ((P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases E.sixResidualCore_models P.six P.six_weight with he | h
  · obtain ⟨e⟩ := he
    exact Or.inl (six_centralizers_of_simple_core P structural e P.six P.six_weight)
  · exact Or.inr h

/-- Actual LocalAnalysis consumer; the remaining weight-two source obligations stay explicit. -/
def localAnalysis_of_simple_six_core (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (B2 : TwoInput P) : S.LocalAnalysis :=
  localAnalysis P (sixInput_of_simple_core P structural e6) B2 structural
    (E.sylow_normalizer_le_component structural)

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
