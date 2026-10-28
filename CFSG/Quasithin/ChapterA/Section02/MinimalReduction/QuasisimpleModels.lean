module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleException
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# Full Theorem B membership for a quasisimple central quotient

Apply the original Theorem A to the literal central quotient. Its ordinary
alternative supplies the local ranks needed for Theorem B; its exceptional
unitary pair supplies a Bender model directly. Thus quasithinness is never
assumed to pass to an arbitrary quotient. Both earlier source theorems remain
explicit, with their full model lists.

Source: Aschbacher--Smith A.2.15 and the component choice preceding 4.4.10,
printed pp.37--38 and 621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {κ : GroupClass.{u}} {Q : Type u} [Group Q] [Finite Q] [IsQuasisimple Q]

/-- The genuine A/B source inputs classify the actual simple central quotient. -/
theorem quasisimple_centralQuotient_theoremBModel
    (hA : TheoremA κ Q) (hB : TheoremB κ (Q ⧸ center Q))
    (hQ : IsQuasithin Q) (hκ : IsKGroup κ Q) :
    IsTheoremBModel (Q ⧸ center Q) := by
  classical
  let S := Q ⧸ center Q
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  have hsemiQ : componentLayer Q = ⊤ := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup Q).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).symm⟩
  have hsemi : IsSemisimple S :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _) hsemiQ
  have hsec : IsSectionOf S Q :=
    IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center Q))
  by_cases he : ∃ p, TheoremAException Q S p
  · obtain ⟨p, hp⟩ := he
    exact hp.theoremBModel_of_simple
  · have hqt : IsQuasithin S := by
      apply isQuasithin_iff_twoLocalPrimeRank.mpr
      intro p hp ho
      have hc := (hA hQ hκ S hsec hsemi p hp ho).1
      exact (hc.resolve_right (fun hh => he ⟨p, hh⟩)).1.trans
        (isQuasithin_iff_twoLocalPrimeRank.mp hQ p hp ho)
    exact hB inferInstance (Group.IsPerfect.not_isMulCommutative S) hqt (hκ.quotient _)
end CFSG.Quasithin.ChapterA.Section02
