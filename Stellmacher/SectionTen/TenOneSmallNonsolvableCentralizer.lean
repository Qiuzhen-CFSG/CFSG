module
public import Stellmacher.SectionTen.TenOneSmallFinalPathContradiction
public import Stellmacher.SectionTen.TenOneSmallTerminalCenterFusion
/-!
# The nonsolvable involution centralizer in the small case

For the actual Section Ten context with first neighbor-center module of
order eight and first local quotient SL₂(2), an involution in the middle
two-core outside its center has a nonsolvable full centralizer in the
original ambient group. This is the exact obstruction field of the small
alternative; the generated graph group and ambient embedding stay fixed.

Suppose no required involution exists. Every point of elementary Wstar
outside the middle center is a nonidentity involution, so its full ambient
centralizer is solvable. The proved small solvable-centralizer theorem
then gives the functional containment in the mapped middle stabilizer.
The actual native involution reduction and terminal-center fusion theorem
supply the other two premises of the completed eight-edge path
contradiction. Hence the assumed absence of the required point is
impossible. All geometric, quotient-action and fusion producers are
proved imports; no classification conclusion is an extra premise.

Source: Stellmacher (10.1)(a3), Journal of Algebra190 (1997), printed
pp.61–62, especially (10), (11), and the final path argument. The separate
small-alternative module combines this witness with the structural data.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G→*H} {T A B : Subgroup G}
public theorem ten_one_small_nonsolvable_centralizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃point:G,Later.IsInvolution point ∧ point∈QAt ctx.Γ middle ∧
      point∉ZAt ctx.Γ middle ∧
      ¬Group.IsSolvable (centralizer ({embedding point}:Set H)) := by
  have hreduce := ten_one_small_commuting_involution_conjugate_wstar ctx middle hpath hsmall hmodel
  by_contra hnone
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := QAt ctx.Γ middle ⊓ centralizer (W0:Set G)
  let _ : IsElementaryAbelian 2 Wstar :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.1
  have hcontain (a:G) (haW:a∈Wstar) (haZ:a∉ZAt ctx.Γ middle) :
      centralizer ({embedding a}:Set H)≤(GAt ctx.Γ middle).map embedding := by
    apply ten_one_small_solvable_centralizer_le_middle ctx middle hpath hsmall hmodel a haW haZ
    by_contra hn
    have hane : a≠1 := by intro heq; exact haZ (heq ▸ (ZAt ctx.Γ middle).one_mem)
    exact hnone ⟨a,⟨hane,elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Wstar) a haW⟩,
      haW.1,haZ,hn⟩
  have hfusion := ten_one_small_terminal_center_fusion ctx middle hpath hsmall hmodel hcontain
  exact ten_one_small_final_path_contradiction ctx middle hpath hsmall hmodel hcontain hfusion hreduce

end Stellmacher.SectionTen
