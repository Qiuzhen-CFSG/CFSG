module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TwoCore
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The full source catalogue on the reduced component

The ordinary component in H/O₂(H) is SQTK. Its simple central quotient is
a semisimple section, so the genuine Theorem A preserves strong quasithinness
there. The completed Theorem C then supplies its full model catalogue,
including the odd-characteristic, alternating and sporadic rows.

This theorem classifies that actual central quotient; it does not identify
the covering center or classify its outside prime automorphism. Those are the
remaining source branches of normal split-prime A.3.18.
Source: Aschbacher–Smith A.2.1, A.2.3 and A.3.18, pp.33,51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

theorem twoCore_central_quotient_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    Section02.IsTheoremCModel (twoCoreComponent K ⧸ center (twoCoreComponent K)) := by
  let B := twoCoreComponent K
  let := (twoCore_isComponent hK).2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hB := (twoCore_sqtk hH).subgroup B
  have hsemiB : componentLayer B = ⊤ := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup B).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm⟩
  have hsemi : Section02.IsSemisimple (B ⧸ center B) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center B))
      (QuotientGroup.mk'_surjective _) hsemiB
  have hsec : Section02.IsSectionOf (B ⧸ center B) B :=
    Section02.IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center B))
  have hq := Section02.theoremA_knownSimple.stronglyQuasithin_section
    hB.stronglyQuasithin hB.isKGroup hsec hsemi
  exact Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hq (hB.isKGroup.quotient _)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
