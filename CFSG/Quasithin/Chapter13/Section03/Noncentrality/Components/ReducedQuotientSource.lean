module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.OffenderSource
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Basic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
/-!
# B.5 on the original reduced module and its centralizer quotient

Set W=R₂(J) and retain the literal quotient J/C_J(W). Reducedness gives
its trivial two-core; the original conjugation map is faithful. Restrict
to the actual normal offender subgroup and apply the complete B.5
classification with the original J as its SQTK cover. Every alternative
is retained. The natural-source application obtains SQTK from the actual
point normalizer and its original subgroup J.

This supplies the correct full B.5 entry in 13.3.14. It does not assert
that J itself is faithful or core-free, or that an arbitrary [W,K] has
the same kernel. Extracting the selected component's moved-module row
remains the subsequent source argument.
Source: Aschbacher–Smith, 13.3.14(f–g), printed pp.892–893.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]
theorem source_reduced_quotient_classification
    (J : Subgroup G) (hJ : IsSQTK KnownSimple.IsKnownSimple J) :
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ : Representation (ZMod 2) (J ⧸ C) (Additive W) := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  let W := reducedTwoSubgroup J
  have hW : IsPReduced 2 W := isPReduced_reducedPSubgroup
  let := hW.elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ : Representation (ZMod 2) (J ⧸ C) (Additive W) := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  change ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype)
  apply ChapterB.offender_restriction_classification ρ
    ChapterB.SourceInduction.adequateClassification_knownSimple
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    hW.quotient_pCore_eq_bot
  exact ⟨{ Cover := J, kernel := C, sqtk := hJ, equiv := MulEquiv.refl _ }⟩

theorem natural_source_reduced_quotient_classification
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V P E U M H)
    (J : Subgroup G) (hJH : J ≤ H) :
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ : Representation (ZMod 2) (J ⧸ C) (Additive W) := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  have hne : P ≠ ⊥ := by intro he; have hc := d.line_card; simp [he] at hc
  have htwo : IsTwoLocal H := by
    rw [d.first_normalizer]
    exact ⟨P,hne,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := d.counterexample.qtke.twoLocal_sqtk htwo
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp (hH.subgroup (J.subgroupOf H))
  exact source_reduced_quotient_classification J hJ
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
