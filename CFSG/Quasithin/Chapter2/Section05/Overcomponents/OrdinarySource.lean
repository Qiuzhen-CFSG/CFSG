module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.TwoComponentSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRankLower
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.Ordinary
public import Theory.GroupTheory.NonsolvableTwoLocal
/-!
# The original ordinary-component upgrade in 2.5.19

The source small-component classification supplies simplicity and a Sylow
four subgroup. In the invariant branch this subgroup survives the solvable
two-core quotient, forcing quasisimplicity by A.3.6. In the transposed branch
the proved nonnormal C-component theorem supplies quasisimplicity directly.
Both perfect central lifts preserve the literal orbit and quotient maps.

The earlier assertion that K is a component of C_G(t) is exactly source
2.5.18 and remains explicit until its separate persistence attachment.
Source: Aschbacher–Smith 2.5.19, printed pp.560–561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

/-- The original source component has the rank required in the invariant
branch; its given embedding makes the containing two-component ordinary. -/
theorem source_twoComponent_quasisimple {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Finite E] (hE:IsSQTK KnownSimple.IsKnownSimple E)
    {L:Subgroup E} (hL:L.IsTwoComponent) (f:K→*L) (hf:Function.Injective f) :
    IsQuasisimple L := by
  have hsrc:=ComponentSelection.MathieuSourceSetup.small_source_structure c hG hempty hgen hb
  let : IsSimpleGroup K:=hsrc.2.1
  let : IsQuasisimple K:=(show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  let P:Sylow 2 K:=default
  exact ChapterI.RankTwoSource.twoComponent_quasisimple_of_simple_rank_two hE hL f hf
    ((hsrc.1.sylowTwoShape P).two_le_rank P)

/-- On the actual odd-E orbit, the source two-component alternatives consist
of ordinary components. The earlier component assertion at t is retained
exactly as in `twoComponent_pumpup`, to be supplied by source 2.5.18. -/
theorem source_twoComponent_pumpup_ordinary {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (t i:G) (ht:orderOf t=2) (hti:Commute t i)
    (hKi:K≤centralizer ({i}:Set G))
    (hKt:IsComponentIn K (centralizer ({t}:Set G)))
    (hi:orderOf i=2) :
    ∃htI:t∈centralizer ({i}:Set G),
      let Gi:=centralizer ({i}:Set G)
      let tI:Gi:=⟨t,htI⟩
      let D:=K.subgroupOf Gi
      let X:=componentOrbit D (oddELayer Gi)
      (IsComponent Gi X ∧ X.map (MulAut.conj tI).toMonoidHom=X) ∨
        ∃J:Subgroup Gi,IsComponent Gi J ∧ J≠J.map (MulAut.conj tI).toMonoidHom ∧
          X=J⊔J.map (MulAut.conj tI).toMonoidHom ∧
          Nonempty ((J⧸oddTwoCore J)≃*(K⧸oddTwoCore K)) := by
  have hGi:=hG.twoLocal_sqtk (Theory.GroupTheory.isTwoLocal_involution_centralizer hi)
  obtain ⟨htI,hKGi,hcases⟩:=twoComponent_pumpup K t i ht hti hKi hKt
  let Gi:=centralizer ({i}:Set G)
  let tI:Gi:=⟨t,htI⟩
  let D:=K.subgroupOf Gi
  let X:=componentOrbit D (oddELayer Gi)
  refine ⟨htI,?_⟩
  rcases hcases with ⟨hX,hfix⟩|⟨J,hJ,hne,hX,he⟩
  · let e:D≃*K:=subgroupOfEquivOfLe hKi
    let f:K→*X:=(inclusion (le_componentOrbit D (oddELayer Gi))).comp e.symm.toMonoidHom
    have hf:Function.Injective f:=(inclusion_injective (le_componentOrbit D (oddELayer Gi))).comp e.symm.injective
    exact Or.inl ⟨⟨hX.1.subnormal,source_twoComponent_quasisimple c hG hempty hgen hb hGi hX f hf⟩,hfix⟩
  · have hn:¬J.Normal := fun h=>hne ((normal_iff_map_conj_eq.mp h tI).symm)
    exact Or.inr ⟨J,⟨hJ.1.subnormal,
      ChapterI.RankTwoSource.twoComponent_quasisimple_of_not_normal hGi hJ hn⟩,hne,hX,he⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
