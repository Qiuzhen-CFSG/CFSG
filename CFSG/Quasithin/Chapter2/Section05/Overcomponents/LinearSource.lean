module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks
public import Theory.SpecificGroups.PSL3Even.FixedComponents
public import Theory.GroupTheory.PrimeRankSylow
/-!
# The binary linear-three overcomponent in source 2.5.19

The original small-component source theorem supplies the actual Sylow shape.
Transporting the component and actor through the containing linear model then
forces PSL₃(4), with the original component PSL₃(2). The output retains the
field action on this same model. Ordinary component placement in the fixed
group is the earlier pumpup step, explicitly retained at this interface.

Source: Aschbacher–Smith 2.5.8(3), p.556, and 2.5.19(3)(II)(a), p.561.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentSelection ComponentRefinement Matrix.PSL3Even.InvolutionResidualRows

/-- A literal fixed component with the source Sylow shape identifies the
linear containing model and retains the actual field-involution marking. -/
theorem linear_fixed_component_of_sylow_shape {E:Type*} [Group E] [Finite E]
    {n:ℕ} (hn:0<n) (hm:ClassicalGroup.IsPSL E 3 (2^n))
    (a:MulAut E) (ha:orderOf a=2)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B)
    (P:Sylow 2 B) (hP:SourceSylowTwoShape P) :
    n=2 ∧ Nonempty (B≃*Matrix.PSL3Two.PSL) ∧
      ∃ (F:Type) (_:Field F) (_:Finite F), Nat.card F=2^n ∧
        ∃e:E≃*PSL(3,F), FieldCase n (MulAut.congr e a) := by
  obtain ⟨F,hField,hFinite,hF,⟨e⟩⟩:=hm
  let ef:=MulAut.fixedSubgroupCongr e a
  let C:=B.map ef.toMonoidHom
  let eB:B≃*C:=ef.subgroupMap B
  let Q:=P.mapSurjective (f:=eB.toMonoidHom) eB.surjective
  let eP:P≃*Q:=(P:Subgroup B).equivMapOfInjective eB.toMonoidHom eB.injective
  have hQ:=hP.of_mulEquiv eP.symm
  have hrank:primeRank 2 C≤2:=by rw [Q.primeRank_eq];exact hQ.rank_and_involutions.1
  obtain ⟨hn2,hfield,⟨ec⟩⟩:=Matrix.PSL3Even.FixedComponents.component_field_degree_two
    hn hF (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)
    C (hB.map_equiv ef) hrank Q hQ.rank_and_involutions.2
  exact ⟨hn2,⟨eB.trans ec⟩,F,hField,hFinite,hF,e,hfield⟩

/-- Source application on the actual selected component. No model list or
Sylow-shape conclusion is assumed for the smaller component. -/
theorem source_binary_linear_fixed_component {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Finite E] {n:ℕ} (hn:0<n)
    (hm:ClassicalGroup.IsPSL E 3 (2^n)) (a:MulAut E) (ha:orderOf a=2)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B) (eK:K≃*B) :
    n=2 ∧ Nonempty (K≃*Matrix.PSL3Two.PSL) ∧
      ∃ (F:Type) (_:Field F) (_:Finite F), Nat.card F=2^n ∧
        ∃e:E≃*PSL(3,F), FieldCase n (MulAut.congr e a) := by
  let P:Sylow 2 K:=default
  let Q:=P.mapSurjective (f:=eK.toMonoidHom) eK.surjective
  let eP:P≃*Q:=(P:Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective
  have hP:SourceSylowTwoShape P:=
    (ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape P
  obtain ⟨hn2,⟨eB⟩,hfield⟩:=linear_fixed_component_of_sylow_shape hn hm a ha B hB Q
    (hP.of_mulEquiv eP.symm)
  exact ⟨hn2,⟨eK.trans eB⟩,hfield⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
