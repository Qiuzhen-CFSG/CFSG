module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwo
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowModelsRecognition
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowNormalizer

/-!
# LocalAnalysisCentralizersSixSource at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersSixSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

def sourceModels_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : P.Models :=
  P.models_of_quotients P.fiveCoreEquiv
    (E.sixResidualCentralEquiv P.six P.six_weight) (P.six_core_eq_core_at structural)

theorem six_source_section_sylow_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ R : Sylow 2 (PointCentralizers.Y (L := L) P.six),
      (R : Subgroup _).map (PointCentralizers.Y (L := L) P.six).subtype =
        PointCentralizers.Q T L :=
  P.six_section_sylow_of_core_eq (P.six_core_eq_core_at structural)

end SylowNormalizer.Points

namespace PointCentralizers

theorem sixInput_of_normalizes_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    P.six_source_section_sylow_at structural⟩

theorem six_centralizer_le_of_normalizes_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hn : H P.six ≤ normalizer (P.sixGroup : Set G)) :
    H P.six ≤ normalizer (L : Set G) :=
  six_centralizer_le_at P (sixInput_of_normalizes_at P structural hn) structural

theorem sixInput_of_simple_core_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    SixInput P := by
  apply sixInput_of_normalizes_at P structural
  simpa only [one_mul] using
    (P.cosetComponents_of_source_at structural (P.sourceModels_at structural) e6).normalizes
      1 P.fixed.one_mem

theorem six_centralizers_of_simple_core_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  E.centralizer_le_of_same_weight v P.six (hv.trans P.six_weight.symm)
    (six_centralizer_le_at P (sixInput_of_simple_core_at P structural e6) structural)

theorem six_centralizer_le_or_triple_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    H P.six ≤ normalizer (L : Set G) ∨
      Nonempty ((P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases E.sixResidualCore_models P.six P.six_weight with he | h
  · obtain ⟨e⟩ := he
    exact Or.inl (six_centralizers_of_simple_core_at P structural e P.six P.six_weight)
  · exact Or.inr h

def localAnalysis_of_simple_six_core_at (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    (B2 : TwoInput P) : S.LocalAnalysis :=
  localAnalysis_at P (sixInput_of_simple_core_at P structural e6) B2 structural
    (E.sylow_normalizer_le_component_at structural)

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

