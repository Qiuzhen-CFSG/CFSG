module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.PerfectCentralCoverOuter
/-!
# Soluble outer automorphisms of quasisimple SQTK sections

The simple central quotient is a semisimple section of the original SQTK
group. The proved Theorems A and C therefore supply its full-catalogue
outer-solvability input. Perfect central descent embeds the outer group of
the original cover into that simple quotient's outer group.

This retains the actual section map needed in the constrained component
argument, Aschbacher--Smith C.4.4--5, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
universe u
variable {G : Type u} [Group G] [Finite G]

theorem quasisimple_section_outer_solvable
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {Q : Type u} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hQ : Section02.IsSectionOf Q G) : Group.IsSolvable (MulAut.Outer Q) := by
  let S := Q ⧸ center Q
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  have hna : ¬ IsMulCommutative S := Group.IsPerfect.not_isMulCommutative S
  have hc : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (hna (center_eq_top_iff.mp hc)).elim
  let : IsQuasisimple S := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hsem : Section02.IsSemisimple S := by
    apply top_unique
    exact le_sSup (show IsComponent S ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec : Section02.IsSectionOf S G :=
    (Section02.IsSectionOf.of_surjective (QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)).trans hQ
  have hsq : IsSQTK KnownSimple.IsKnownSimple S :=
    ⟨Section02.theoremA_knownSimple.stronglyQuasithin_section
      hG.stronglyQuasithin hG.isKGroup hsec hsem,hsec.isKGroup hG.isKGroup⟩
  let : Group.IsSolvable (MulAut.Outer S) :=
    (source_model_inputs_of_theoremC
      (fun X _ _ => Section02.theoremC_knownSimple (G := X)) S inferInstance hna hsq).1
  exact Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (Q ⧸ center Q)))

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
