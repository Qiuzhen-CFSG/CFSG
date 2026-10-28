module
public import Theory.SpecificGroups.Triality.InvolutionFixedComponents
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks
public import Theory.GroupTheory.PrimeRankSylow
/-!
# Excluding every triality overcomponent in source 2.5.19

The original source theorem gives simplicity and the actual dihedral or
semidihedral Sylow shape of K. In the inner row, its embedding in the fixed
group would force a commutative Sylow two-subgroup. In the outer row, the
literal ordinary fixed component has two-rank 5m, contradicting K's rank two.
Both branches keep the original model equivalence, actor and fixed-component
map. No involution-table, parabolic-containment, or Sylow-shape premise is added.

Source: Aschbacher–Smith 2.5.19, p.561, using 2.5.8(3) and 16.1.4(1,4).
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection Triality.Standard

/-- The exact outer fixed-component row on the original source K. -/
theorem source_not_outer_triality_fixed_component {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Finite E] {n:ℕ} (hn:0<n)
    (hm:IsTrialityGroupAt (2^n) E) (a:MulAut E) (ha:orderOf a=2)
    (hout:∀g:E,a≠MulAut.conj g)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B) (eK:K≃*B) : False := by
  obtain ⟨e⟩:=(isTrialityGroupAt_binary_iff E n hn).mp hm
  have hr:=EvenField.outer_fixed_component_rank_gt_two_of_equiv n hn e a ha hout B hB
  let P:Sylow 2 K:=default
  have hP:SourceSylowTwoShape P:=
    (ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape P
  have hrK:primeRank 2 K≤2:=by rw [P.primeRank_eq];exact hP.rank_and_involutions.1
  rw [←primeRank_equiv 2 eK] at hr
  omega
end CFSG.Quasithin.Chapter2.Section05.Overcomponents

namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection Triality.Standard

/-- Every triality involution row is excluded for the original source K. -/
theorem source_not_triality_fixed_component {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Finite E] {n:ℕ} (hn:0<n)
    (hm:IsTrialityGroupAt (2^n) E) (a:MulAut E) (ha:orderOf a=2)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B) (eK:K≃*B) : False := by
  obtain ⟨e⟩:=(isTrialityGroupAt_binary_iff E n hn).mp hm
  let a':=MulAut.congr e a
  have ha':orderOf a'=2:=((MulAut.congr e).orderOf_eq a).trans ha
  let ef:=MulAut.fixedSubgroupCongr e a
  let P:Sylow 2 K:=default
  have hs:=ComponentSelection.MathieuSourceSetup.small_source_structure c hG hempty hgen hb
  have hP:SourceSylowTwoShape P:=hs.1.sylowTwoShape P
  by_cases hi:a'∈MulAut.innerSubgroup (BinaryCarrier n hn)
  · let : IsSimpleGroup K:=hs.2.1
    let : IsQuasisimple K:=(show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
    let f:K→*a'.fixedSubgroup:=ef.toMonoidHom.comp (B.subtype.comp eK.toMonoidHom)
    have hf:Function.Injective f:=ef.injective.comp (B.subtype_injective.comp eK.injective)
    let : IsMulCommutative P:=InvolutionFixedComponents.sylow_commutative_of_simple_inner_fixed_embedding
      n hn a' ha' hi f hf P
    exact hP.rank_and_involutions.2 (fun x y _ _=>Commute.all x y)
  · let D:=B.map ef.toMonoidHom
    let d:K≃*D:=eK.trans (ef.subgroupMap B)
    have hr:=EvenField.outer_fixed_component_rank_gt_two n hn a' ha' hi D (hB.map_equiv ef)
    have hrK:primeRank 2 K≤2:=by rw [P.primeRank_eq];exact hP.rank_and_involutions.1
    rw [←primeRank_equiv 2 d] at hr
    omega
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
