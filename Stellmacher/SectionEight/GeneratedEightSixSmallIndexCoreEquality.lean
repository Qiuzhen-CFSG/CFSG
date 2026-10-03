module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCoreEqualityTools

/-!
# SmallIndexCoreEquality in the small-index branch of (8.6)

The small-index equation-one data identify the generated core with the initial vertex
core. Coprime fixed-core control and cyclicity of the first-core quotient center force
the reverse containment; the equation-one containment supplies the other direction.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_core_eq_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = SectionsFiveToSeven.conjugateClosure
        (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hquotient : QuotientCardEq Q D 4)
    (_hintersection : D ⊓ CenterAmbient Q = ZAt ctx.Γ ctx.criticalPath.a)
    (_hcenterindex : QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 1 ∨
      QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 2) :
    Q = QAt ctx.Γ ctx.criticalPath.a := by
  let _ : ((QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      S).Normal :=
    eight_six_first_core_normal_in_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath
  let projection := QuotientGroup.mk'
    ((QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf S)
  have hsurjective : Function.Surjective projection := QuotientGroup.mk'_surjective _
  have hkernel : projection.ker = (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      S := QuotientGroup.ker_mk' _
  have hfixed := eight_six_fixed_core_le_of_three_sylow_transitivity ctx.Γ ctx.criticalPath
    previous D L Q T hprev.1 hdefs.2.1 hdefs.2.2.1 hdefs.2.2.2 data hindex hquotient
    (cubic_three_sylow_transitive ctx.sectionSeven ctx.Γ ctx.criticalPath.a hquot T hdefs.2.2.2)
  have hcyclic := eight_six_first_core_quotient_center_isCyclic
    ctx.sectionSeven ctx.Γ ctx.criticalPath projection hsurjective hkernel
  apply le_antisymm
  · exact (eight_six_equation_one_core_containments ctx.Γ ctx.criticalPath
      previous D L Q data hbase.2.2).2.2
  · exact (eight_six_core_eq_of_fixed_core_and_cyclic_center ctx
      hlength hcard previous D L Q T hprev.1 hdefs.1 hdefs.2.1 hdefs.2.2.1
      hdefs.2.2.2 data hindex hfixed projection hsurjective hkernel hcyclic).ge

public theorem generated_eight_six_small_index_core_eq
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = SectionsFiveToSeven.conjugateClosure
        (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hquotient : QuotientCardEq Q D 4)
    (_hintersection : D ⊓ CenterAmbient Q = ZAt ctx.Γ ctx.criticalPath.a)
    (_hcenterindex : QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 1 ∨
      QuotientCardEq D (ZAt ctx.Γ ctx.criticalPath.a) 2) :
    Q = QAt ctx.Γ ctx.criticalPath.a := by
  exact eight_six_small_index_core_eq_local ctx.toLocalContext
    _hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data hquotient _hintersection _hcenterindex

end Stellmacher.SectionEight
