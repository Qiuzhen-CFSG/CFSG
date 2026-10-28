module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InnerSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import GorensteinWalter.PSL2Center
public import Theory.SpecificGroups.LinearCoefficientEquiv
/-! # The sole surviving source component with nontrivial center
The complete original model-action classification makes the component
centerless except for its PSL₃(4) central cover. The source excludes the
alternating outer cases and the G₂(4) cover; the remaining sporadic row is
the actual centerless M₁₁. Thus an arbitrary linear central-quotient marking
can enter the proved simple or exceptional field-reduction branch.
Source: Aschbacher--Smith 2.5.2 and the opening of 2.5.7, pp.551,554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
open Chapter15.Section03.Candidates.ComponentStructure
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

private theorem center_trivial_of_equiv {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) (hY:center Y=⊥) : center X=⊥ := by
  apply bot_unique
  intro x hx
  have hh:e x∈center Y:=(centerCongr e ⟨x,hx⟩).property
  rw [hY,mem_bot] at hh
  exact e.injective (hh.trans e.map_one.symm)

omit [Finite G] in
private theorem four_model_equiv
    (hm:ClassicalGroup.IsPSL (L⧸center L) 3 4) :
    Nonempty (L⧸center L≃*Matrix.PSL3Four.PSL) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
  let :=Fintype.ofFinite F
  let :=Fintype.ofFinite Matrix.PSL3Four.F
  let eF:F≃+*Matrix.PSL3Four.F:=FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)⟩

/-- Every original source component is centerless or an actual PSL₃(4) cover. -/
theorem MathieuSourceSetup.center_eq_bot_or_linear_four
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅) :
    center L=⊥ ∨ Nonempty (L⧸center L≃*Matrix.PSL3Four.PSL) := by
  let h:=c.localSetup hG structural115Input localC129Input_knownSimple
  let :=h.quasisimple
  obtain ⟨α,hα,hm⟩:=c.modelAction115_knownSimple hG
  cases hm with
  | lie hs _ _ =>
    let :=hs
    exact Or.inl center_eq_bot_of_simple_perfect
  | two_cover hn hc hm hi =>
    rcases hm with hm|hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
      exact Or.inr (four_model_equiv ⟨F,inferInstance,inferInstance,hF,
        ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e⟩⟩)
    · have hinner:∃t:L,IsConjugationProjection L z t:=by
        obtain ⟨t,rfl⟩:=hi
        exact ⟨t,fun a=>(hα a).symm⟩
      obtain ⟨F,_,_,hF,he⟩:=hm
      exact (LieType.G2.not_central_quotient_model h hinner hc (hc ▸ hn) F hF he).elim
  | six σ hσ ha =>
    exact (alternating_six_action_false c.gamma hempty h α hα σ hσ ha).elim
  | seven σ hσ ha =>
    exact (alternating_seven_action_false c.gamma hempty h α hα σ hσ ha).elim
  | odd hm _ =>
    apply Or.inl
    rcases hm with hm|⟨p,_,hm⟩
    · obtain ⟨F,_,_,_,⟨e⟩⟩:=hm
      let :=Atlas.sl_perfect (F:=F) 3 (by decide)
      exact center_trivial_of_equiv e (Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F)))
    · obtain ⟨F,_,_,_,⟨e⟩⟩:=hm
      exact center_trivial_of_equiv e (GorensteinWalter.psl2_center_eq_bot F)
  | sporadic name hn hm hi =>
    obtain ⟨e₀⟩:=hm
    obtain ⟨e⟩:=sporadic_model_of_emptyGamma c hG localC129Input_knownSimple hempty hn ⟨e₀,α,hα,hi.1⟩
    let : IsSimpleGroup Sporadic.Mathieu.M11:=Sporadic.Mathieu.m11_isSimpleGroup
    let : IsSimpleGroup L:=e.isSimpleGroup
    exact Or.inl center_eq_bot_of_simple_perfect
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
