module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The genuine B.4.2 source domain and Theorem C reduction

A best offender supplies the Chapter K cubic bound by the proved replacement
theorem. Theorem A gives strong quasithinness of the literal central quotient
of the quasisimple layer; its actual section map also transports the full
K-group hypothesis. Theorem C then supplies the complete group catalogue.
Neither a representation classification nor a restricted catalogue is assumed.

Source: Aschbacher--Smith B.4.2 and Chapter K introduction, pp.86 and 451.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem source_hypotheses (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    (hff : IsFFModule ρ) : ChapterK.RankOne.SourceHypotheses ρ L := {
  sqtk := hsq
  fitting := hfit
  quasisimple := hL
  faithful := hf
  irreducible := hi
  smallCubic := (cubicRatio_le_quadraticRatio ρ).trans
    (((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num)) }

theorem source_hypotheses_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A) : ChapterK.RankOne.SourceHypotheses ρ L :=
  source_hypotheses hsq hfit hL hf hi ⟨A,hA.isOffender ρ⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem quotient_model_of_theoremsAC
    (hA : ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple G)
    (hC : ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple (L ⧸ center L))
    (h : ChapterK.RankOne.SourceHypotheses ρ L) :
    ChapterA.Section02.IsTheoremCModel (L ⧸ center L) := by
  let := h.quasisimple
  let S := L ⧸ center L
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  let : IsQuasisimple S := IsQuasisimple.of_surjective (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective (center L))
  have hsem : ChapterA.Section02.IsSemisimple S := by
    apply top_unique
    exact le_sSup (show IsComponent S ⊤ from
      ⟨(inferInstance : (⊤ : Subgroup S).Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec := ChapterA.Section02.IsSectionOf.quotient_subgroup L (center L)
  have hsq := hA.stronglyQuasithin_section h.sqtk.stronglyQuasithin h.sqtk.isKGroup hsec hsem
  exact hC inferInstance (Group.IsPerfect.not_isMulCommutative S) hsq
    (hsec.isKGroup h.sqtk.isKGroup)
end CFSG.Quasithin.ChapterB.SourceClassification
