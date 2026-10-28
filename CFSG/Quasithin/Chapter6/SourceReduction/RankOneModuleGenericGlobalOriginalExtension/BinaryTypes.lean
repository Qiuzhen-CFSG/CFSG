module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# Rejecting binary quotient types in the original perfect pair

A PSL₂(2) quotient by the intrinsic two-core makes its finite group solvable.
For a selected local factor, the genuine F.1.1 residual/quotient theorem then
makes its entire source parabolic solvable. For a full parabolic quotient the
contradiction is immediate. Both conflict with the nonsolvability already
proved for every prepared perfect selected pair.

These distinct quotient conventions cover the binary type clauses without
asserting an isomorphism from an abstract type to a Tits or Ree model. The
Chapter 12 consumer removes these clauses in either source orientation.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

include d h hTH hp in
/-- A binary type clause on a selected local factor is already impossible;
no identification of that type with a global binary Ree model is needed. -/
theorem Preparation.not_binary_factor_quotient (i : Fin 2) :
    ¬ ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  have hs := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact d.parabolics_not_solvable h hp i
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient i).mpr hs)

include d h hp in
/-- A binary type clause on a full original endpoint is also impossible.
Its intrinsic two-core is kept distinct from the selected factor's core. -/
theorem Preparation.not_binary_parabolic_quotient (i : Fin 2) :
    ¬ ClassicalGroup.IsPSL
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i ⧸
        pCore 2 (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)) 2 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  exact d.parabolics_not_solvable h hp i
    ((Group.isSolvable_iff_subgroup_quotient (pCore 2 P)).mpr
      ⟨inferInstance,Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
