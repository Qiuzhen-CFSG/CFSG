module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Algebra
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.EvenModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.FiniteModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.OddModels
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Excluding rank-one components using an extraspecial three-subgroup

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137, and Theorems A/C (A.2.1/A.2.3), printed p.33.

`Algebra` proves normalization, deals with central covers, and constructs
the elementary subgroup of order 27 from an abelian action image. Here
Theorem A passes strong quasithinness to the genuine semisimple quotient
J/Z(J); section inheritance supplies its K-group hypothesis. Theorem C then
identifies that quotient using actual multiplicative equivalences.

The three model modules prove that every exponent-three subgroup of the
actual automorphism group of a simple rank-one entry of Theorem C is abelian.
`cubic_of_theoremC_model` assembles every constructor, including the small
derived groups and Tits. `component_rank_ne_one` consequently proves the
local extraspecial exclusion with only the earlier source Theorems A and C
as explicit inputs. The parent must supply A.2.1 on H and universal A.2.3;
no intrinsic model or automorphism premise remains.

The SQTK parameter is the full known-simple catalogue. No normality of B or
J, no four-group centralized by B, and no multiplier classification are
assumed. Components.lean and its existing siblings remain the parent's API.
-/

public section

open Subgroup Theory.GroupTheory CFSG.Quasithin CFSG.Quasithin.ChapterA.Section02
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The genuine simple central quotient is in Theorem C, using exactly the
explicit earlier A.2.1 and universal A.2.3 propositions. Semisimplicity,
strong quasithinness and the K-group condition are all established here. -/
theorem component_central_quotient_model
    {κ : GroupClass} (hA : TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], TheoremC κ S)
    (hH : IsSQTK κ H) (J : Subgroup H) (hJ : IsComponent H J) :
    IsTheoremCModel (J ⧸ center J) := by
  let := hJ.2
  let S := J ⧸ center J
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : IsQuasisimple S := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center J)) (QuotientGroup.mk'_surjective _)
  have hsem : IsSemisimple S := by
    apply top_unique
    apply le_sSup
    exact ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have hsection : IsSectionOf S H := IsSectionOf.quotient_subgroup J (center J)
  have hsq := hA.stronglyQuasithin_section hH.stronglyQuasithin hH.isKGroup hsection hsem
  exact hC S inferInstance (Group.IsPerfect.not_isMulCommutative S) hsq
    (hsection.isKGroup hH.isKGroup)

/-- Every rank-one nonabelian simple entry of the genuine Theorem C list has
abelian exponent-three subgroups in its actual automorphism group. -/
theorem cubic_of_theoremC_model {S : Type u} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (hmodel : IsTheoremCModel S)
    (hr : primeRank 3 S = 1) : CubicAutomorphismsAbelian S := by
  cases hmodel with
  | alternating _ hn iso => exact FiniteModels.cubic_alternating hna hr hn iso
  | odd model => exact cubic_of_odd_model hna hr model
  | bender model => exact cubic_of_bender model hr
  | rank_two _ model => exact cubic_of_rank_two hna model hr
  | linear_binary _ hn iso => exact cubic_of_linear_binary hn iso hr
  | sporadic model => exact FiniteModels.cubic_sporadic hna hr model

/-- The local extraspecial exclusion, conditional on the intrinsic model
automorphism calculation. The source inputs are Theorem A on H and Theorem C
for finite groups in the same universe, with their hypotheses retained inside
those propositions. The final `component_rank_ne_one` supplies `hAut` from
the complete model inspection above. -/
theorem component_rank_ne_one_of_model_automorphisms
    (hA : TheoremA CFSG.KnownSimple.IsKnownSimple H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], TheoremC CFSG.KnownSimple.IsKnownSimple S)
    (hAut : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S →
      ¬ IsMulCommutative S → IsTheoremCModel S → primeRank 3 S = 1 →
      CubicAutomorphismsAbelian S)
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple H)
    (B : Subgroup H) [IsExtraspecial 3 B] (hc : Nat.card B = 27)
    (he : ∀ b : B, b ^ 3 = 1) (J : Subgroup H) (hJ : IsComponent H J) :
    primeRank 3 J ≠ 1 := by
  intro hr
  let := hJ.2
  let S := J ⧸ center J
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center J)) (QuotientGroup.mk'_surjective _)
  have hSr := central_quotient_rank_one hr
  have ha : CubicAutomorphismsAbelian S := hAut S inferInstance
    (Group.IsPerfect.not_isMulCommutative S)
    (component_central_quotient_model hA hC hH J hJ) hSr
  exact rank_one_excluded_of_cubic B J hc he hJ
    (hH.stronglyQuasithin 3 (by decide) (by decide)) ha hr

/-- The extraspecial rank obstruction used in 15.3.38, printed p.1137.
The explicit earlier-source inputs are A.2.1 on H and universal A.2.3,
both with the full known-simple catalogue. Their own quasithinness, section,
semisimplicity, simplicity and K-group premises are discharged in
`component_central_quotient_model`. No normalization or centralizing
four-group hypothesis is imposed on B; J is an ordinary component. -/
theorem component_rank_ne_one
    (hA : TheoremA CFSG.KnownSimple.IsKnownSimple H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], TheoremC CFSG.KnownSimple.IsKnownSimple S)
    (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple H)
    (B : Subgroup H) [IsExtraspecial 3 B] (hc : Nat.card B = 27)
    (he : ∀ b : B, b ^ 3 = 1) (J : Subgroup H) (hJ : IsComponent H J) :
    primeRank 3 J ≠ 1 := by
  apply component_rank_ne_one_of_model_automorphisms hA hC _ hH B hc he J hJ
  intro S _ _ hs hna hmodel hr
  let := hs
  exact cubic_of_theoremC_model hna hmodel hr

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
