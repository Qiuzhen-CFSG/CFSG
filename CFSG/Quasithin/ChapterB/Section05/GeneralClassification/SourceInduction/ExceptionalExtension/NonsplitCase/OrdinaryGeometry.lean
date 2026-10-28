module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Inputs

/-!
# Ordinary factors with a fixed supplement in the exceptional endgame

An ordinary B.5.11 factor already implies [V,G₂]+C_V(G)=V₂. Its image in
the global fixed quotient is therefore exactly the image of V₂. The
original quotient maps identify its natural or doubled-natural action
with the supplied factor action, preserving fields and odd degrees.

If C_V(G₂)+V₂=V, choose u fixed by G₂ outside W+V₂. The chosen first
four-space and the actual second moved space then give B.5.6(3) in
V/C_V(G), even if [V,G₂] intersects C_V(G). This distinction matters:
failure of the direct-sum condition SplitAtSecond does not itself imply
failure of this fixed-supplement condition.

The only earlier-source input is the complete EarlierB48Three used to
construct the first factor's full B.4.8(3) record. It is owned by
qt-b-04-natural-extensions. No cohomology or generation is assumed here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and the exceptional endgame, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private def composeAction {A B C X Y Z : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {α : Representation (ZMod 2) A X} {β : Representation (ZMod 2) B Y}
    {γ : Representation (ZMod 2) C Z}
    (e : ActionEquiv α β) (f : ActionEquiv β γ) : ActionEquiv α γ :=
  ⟨e.groupEquiv.trans f.groupEquiv,e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

theorem secondMoved_image_eq (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) :
    (fixed ρ).quotientImage (secondMoved c) =
      (fixed ρ).quotientImage c.productConfiguration.fixed := by
  apply Subrepresentation.toSubmodule_injective
  change (moved ρ (second c)).map ρ.invariants.mkQ =
    c.productConfiguration.fixed.toSubmodule.map ρ.invariants.mkQ
  rw [← second_supplement_of_moved_factor c he f hm,Submodule.map_sup,
    Submodule.mkQ_map_self,sup_bot_eq]

noncomputable def ambientSecondFactorEquiv (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) :
    ActionEquiv (((fixed ρ).quotientImage (secondMoved c)).toRepresentation.comp (second c).subtype)
      (secondFactorAction c f) := by
  let l := LinearEquiv.ofEq _ _
    (congrArg Subrepresentation.toSubmodule (secondMoved_image_eq c he f hm))
  let e : ActionEquiv
      (((fixed ρ).quotientImage (secondMoved c)).toRepresentation.comp (second c).subtype)
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp (second c).subtype) :=
    ⟨MulEquiv.refl _,l,fun _ _ => Subtype.ext rfl⟩
  let p := actionSymm (factorQuotientEquiv c f)
  exact ⟨e.groupEquiv.trans p.groupEquiv,e.linearEquiv.trans p.linearEquiv,
    fun g v => (congrArg p.linearEquiv (e.intertwines g v)).trans (p.intertwines _ _)⟩

theorem ambientSecondFactor_of_ordinary (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c)) (hf : OrdinarySecondFactor c f) :
    SourceFactorCase ρ (second c) (secondMoved c) := by
  let e := ambientSecondFactorEquiv c he f hf.1
  rcases hf.2 with hn | ⟨F,ho,hn⟩
  · apply SourceFactorCase.natural rfl
    cases hn with
    | linearTwo F hn =>
      obtain ⟨n⟩ := hn
      exact .linearTwo F ⟨composeAction e n⟩
    | symmetricFive hn =>
      obtain ⟨n⟩ := hn
      exact .symmetricFive ⟨composeAction e n⟩
    | linearThree F ho hn =>
      obtain ⟨n⟩ := hn
      exact .linearThree F ho ⟨composeAction e n⟩
  · obtain ⟨n⟩ := hn
    exact .doubleNatural F ho rfl ⟨composeAction e n⟩

theorem adequate_of_ordinary_fixed_supplement [Finite G]
    [FiniteDimensional (ZMod 2) V] (h48 : EarlierB48Three.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c)) (hf : OrdinarySecondFactor c f)
    (hs : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤) :
    AdequateAlternative ρ := by
  obtain ⟨x,hxf,hx⟩ := exists_outside_in_supplement c he _ hs
  have hd : ∀ b : second c, ρ (b : G) x - x ∈ ρ.invariants := by
    intro b
    rw [show ρ (b : G) x = x from hxf b,sub_self]
    exact ρ.invariants.zero_mem
  have hx' : x ∉ c.sectionData.space.toSubmodule ⊔ fixedSpace ρ c.first := by
    simpa only [c.productConfiguration.fixed_eq] using hx
  obtain ⟨q₁⟩ := chosenModule_source h48 c.sectionData.space (first_moved c he) he hx'
  obtain ⟨q₁'⟩ := four_source_transport h48 (actionSymm (firstSaturatedEquiv c he x hx hd)) q₁
  refine Or.inr (.twoFactors {
    first := c.first
    second := second c
    product := c.productConfiguration.product
    firstSpace := saturatedModule c he x hd
    secondSpace := secondMoved c
    decomposition := ?_
    firstCase := .exceptional ?_ q₁'
    secondCase := ambientSecondFactor_of_ordinary c he f hf })
  · rw [secondMoved_image_eq c he f hf.1]
    exact saturated_quotient_isCompl c he x hx hd
  · rw [first_moved c he]
    exact le_sup_left.trans le_sup_left

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
