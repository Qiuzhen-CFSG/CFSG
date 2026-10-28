module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenBorel
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ModelSource
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram.Geometry
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.InnerIndexTwo
/-! # The actual binary linear component automizer
The original source Sylow action exchanges the two projective parabolics.
These have distinct inner-conjugacy classes, so that actor is outer.
The proved index two of Inn(PSL₃(2)) then exhausts the full automorphism
group. The quotient conclusion uses the literal normalizer conjugation map.
Source: Aschbacher--Smith 2.5.16(2), printed p.560, using 2.5.2.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Theory.GroupTheory Matrix.PSL3.LinearThree
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {M H:Subgroup G}
theorem linear_binary_normalizer_action_surjective
    (hH:H∈gammaZero (Chapter1.He G) M)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (S:Sylow 2 H) (hSM:(S:Subgroup H).map H.subtype≤M)
    (D:Subgroup H) (hD:IsComponent H D) (hout:¬D.map H.subtype≤M)
    (e₀:D≃*Matrix.PSL3Two.PSL) :
    Function.Surjective D.normalizerMonoidHom := by
  have hk:IsPGroup 2 e₀.toMonoidHom.ker:=by
    rw [e₀.toMonoidHom.ker_eq_bot e₀.injective]
    exact IsPGroup.of_card (n:=0) (by simp)
  obtain ⟨f,hf,_,_,_,s,_,hmove,_⟩:=exists_linear_even_borel_source
    hH hempty S hSM D hD hout (ZMod 2) (n:=1) (by decide) (by norm_num)
    e₀.toMonoidHom e₀.surjective hk
  have hinner:MulAut.innerSubgroup D≤D.normalizerMonoidHom.range:=by
    rintro _ ⟨d,rfl⟩
    refine ⟨⟨d,D.le_normalizer d.property⟩,?_⟩
    ext v
    rfl
  have houter:Nat.card (MulAut.Outer D)=2:=by
    rw [Nat.card_congr (MulAut.outerCongr (e₀.trans Matrix.PSL3Two.equiv.symm)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_outer_sl
  apply MulAut.surjective_of_inner_le_of_outer_card_two _ hinner houter s
  rintro ⟨d,hd⟩
  have hh:=congrArg (Subgroup.map f) hmove
  rw [←hd] at hh
  have hcomp:f.comp (MulAut.conj d).toMonoidHom=(MulAut.conj (f d)).toMonoidHom.comp f:=by
    ext u
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  rw [map_map,hcomp,←map_map,map_comap_eq_self_of_surjective hf,
    map_comap_eq_self_of_surjective hf] at hh
  exact Matrix.PSL3.LinearThree.OuterExtensions.pointParabolic_not_conjugate_line
    (ZMod 2) (n:=1) (by decide) (by norm_num) (f d) hh
variable {L:Subgroup G} {S:Sylow 2 H} {z:G}

/-- The full action on the original relative component, with all source
movement inputs discharged. -/
theorem MathieuSourceSetup.linear_binary_normalizer_action_surjective
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L≃*Matrix.PSL3Two.PSL) :
    Function.Surjective (L.subgroupOf H).normalizerMonoidHom := by
  let D:=L.subgroupOf H
  have hout:¬D.map H.subtype≤M:=((c.hypotheses115 hG).component_inputs D c.component).1
  exact CFSG.Quasithin.Chapter2.Section05.ComponentSelection.linear_binary_normalizer_action_surjective c.gamma hempty S
    (c.hypotheses115 hG).mem_HeOver.2.2 D c.component hout
    ((subgroupOfEquivOfLe c.component_le).trans e)

/-- The literal normalizer quotient is the full automorphism group. -/
theorem MathieuSourceSetup.linear_binary_normalizer_quotient
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L≃*Matrix.PSL3Two.PSL) :
    let D:=L.subgroupOf H
    Nonempty ((normalizer (D:Set H)) ⧸
      (centralizer (D:Set H)).subgroupOf (normalizer (D:Set H)) ≃*
      MulAut Matrix.PSL3Two.PSL) := by
  let D:=L.subgroupOf H
  have hs:=MathieuSourceSetup.linear_binary_normalizer_action_surjective c hG hempty e
  let eD:D≃*Matrix.PSL3Two.PSL:=(subgroupOfEquivOfLe c.component_le).trans e
  exact ⟨(QuotientGroup.quotientMulEquivOfEq D.normalizerMonoidHom_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective D.normalizerMonoidHom hs).trans (MulAut.congr eD))⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
