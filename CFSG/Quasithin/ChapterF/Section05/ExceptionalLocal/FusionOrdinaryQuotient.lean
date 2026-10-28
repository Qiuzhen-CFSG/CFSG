module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceUpper
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerQuotient
/-!
# The ordinary upper subgroup in the graph-centralizer quotient

The ordinary upper image has trivial graph coordinate, whereas the marked
graph involution has nontrivial graph coordinate. Faithfulness therefore
makes the ordinary upper image disjoint from the cyclic graph kernel.
Consequently the literal quotient map is injective on every ordinary upper
subgroup of the graph centralizer, with image the actual mapped subgroup.

This is the quotient-injectivity input for the residual join `U` and its
image `U*` in Aschbacher--Smith F.5.5, pp.301--302. The residual-join owner
supplies its containment in the ordinary upper image and the centralizer.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The literal graph coordinate excludes the marked graph involution from the ordinary upper image. -/
theorem source_graph_not_mem_ordinaryUpper (hi : Function.Injective i) :
    Source.graphElement c i ∉ sourceOrdinaryUpper c i := by
  rintro ⟨a,ha⟩
  have he : ordinaryUpperInclusion a=UnitaryTwo.GraphCentralizer.graphInvolution :=
    c.middle_injective (hi ha)
  have hh := congrArg (fun b : Extension.overlap 1 hn => b.val.right) he
  exact (by decide : (1 : Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.C2) ≠
    Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator) hh

variable [Finite G]

/-- The ordinary upper image has trivial intersection with the actual graph kernel. -/
theorem sourceOrdinaryUpper_disjoint_graph (hi : Function.Injective i) :
    Disjoint (sourceOrdinaryUpper c i) (zpowers (Source.graphElement c i)) := by
  classical
  apply disjoint_def.mpr
  intro x hx hxf
  rw [mem_zpowers_iff_mem_range_orderOf,source_graph_order c i hi] at hxf
  obtain ⟨n,hnn,rfl⟩ := Finset.mem_image.mp hxf
  have hn2 : n<2 := Finset.mem_range.mp hnn
  interval_cases n
  · exact pow_zero _
  · exact False.elim (source_graph_not_mem_ordinaryUpper c i hi (by simpa using hx))

/-- The actual graph-centralizer quotient map restricted to an ambient subgroup. -/
def sourceOrdinaryGraphQuotientMap (K : Subgroup G) (hKC : K≤C c i) :
    K →* graphCentralQuotient c i :=
  (QuotientGroup.mk' (zpowers (graphInCentralizer c i))).comp (inclusion hKC)

/-- Quotienting by the central graph involution is injective on every ordinary upper subgroup. -/
theorem sourceOrdinaryGraphQuotientMap_injective (hi : Function.Injective i)
    (K : Subgroup G) (hKS : K≤sourceOrdinaryUpper c i) (hKC : K≤C c i) :
    Function.Injective (sourceOrdinaryGraphQuotientMap c i K hKC) := by
  apply (sourceOrdinaryGraphQuotientMap c i K hKC).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  apply (mem_bot).mpr
  apply Subtype.ext
  have hxker : (⟨x.val,hKC x.property⟩ : C c i)∈zpowers (graphInCentralizer c i) :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hxin : x.val∈zpowers (Source.graphElement c i) := by
    have hh := mem_map_of_mem (C c i).subtype hxker
    rw [MonoidHom.map_zpowers] at hh
    exact hh
  exact disjoint_def.mp (sourceOrdinaryUpper_disjoint_graph c i hi) (hKS x.property) hxin

/-- The literal quotient image of any ordinary upper subgroup is isomorphic to that subgroup. -/
def sourceOrdinaryGraphQuotientEquiv (hi : Function.Injective i)
    (K : Subgroup G) (hKS : K≤sourceOrdinaryUpper c i) (hKC : K≤C c i) :
    K ≃* ((K.subgroupOf (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i)))) := by
  let q := QuotientGroup.mk' (zpowers (graphInCentralizer c i))
  have he : (sourceOrdinaryGraphQuotientMap c i K hKC).range=(K.subgroupOf (C c i)).map q := by
    rw [sourceOrdinaryGraphQuotientMap,MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  exact (MonoidHom.ofInjective (sourceOrdinaryGraphQuotientMap_injective c i hi K hKS hKC)).trans
    (MulEquiv.subgroupCongr he)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
