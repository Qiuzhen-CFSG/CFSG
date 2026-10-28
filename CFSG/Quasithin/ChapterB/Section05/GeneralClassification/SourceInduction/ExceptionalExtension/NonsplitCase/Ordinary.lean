module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary.Cohomology
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary.BinaryKernel
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary.SymmetricFive
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree

/-!
# Ordinary second-factor reduction in the exceptional nonsplit endgame

The cohomology calculation in Ordinary.Cohomology forces degree one for the
natural and doubled SL₃ rows. The resulting exhaustive sieve retains the
actual natural SL₂ action, the S₅ action, or one or two binary natural SL₃
copies on the original fixed quotient of the factor.

Once the fixed kernel of the ambient second moved space is zero, the literal
quotient projection and secondMovedFactorEquiv lift the binary action. The
one-copy and two-copy cases then give the exact r≤2 clause of B.5.6(5).
The final theorem discharges the S₅ exclusion through splitting over the
literal A₅ core, and the binary fixed kernel through the actual moved-module
cohomology. It proves the ordinary nonsplit second-action conclusion under
the separate case hypothesis C_V(G₂)+V₂<V. The sole earlier-source input is
EarlierB48Four, the faithful indecomposable dimension theorem B.4.8(4), owned
by qt-b-04-natural-extensions. The parent's fixed-supplement case split and
hyperplane geometry complete its AdequateAlternative assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(5),
printed p.105, and its concluding proof, printed p.110, lines 5733–5744.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction

private def compAction {A B C X Y Z : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {α : Representation (ZMod 2) A X} {β : Representation (ZMod 2) B Y}
    {γ : Representation (ZMod 2) C Z}
    (e : ActionEquiv α β) (f : ActionEquiv β γ) : ActionEquiv α γ :=
  ⟨e.groupEquiv.trans f.groupEquiv,e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

private noncomputable def fixedQuotientEquiv
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) (hz : σ.invariants = ⊥) :
    ActionEquiv σ (reducedAction σ) :=
  ⟨MulEquiv.refl _, LinearEquiv.ofBijective σ.invariants.mkQ
    ⟨LinearMap.ker_eq_bot.mp (by rw [Submodule.ker_mkQ, hz]),
      σ.invariants.mkQ_surjective⟩, fun _ _ => rfl⟩

private noncomputable def naturalOneEquiv :
    ActionEquiv (linearNatural BinaryField.two 3)
      (repeated (linearNatural BinaryField.two 3) 1) :=
  ⟨MulEquiv.refl _, (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → ZMod 2)).symm,
    fun _ _ => rfl⟩

universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- All ordinary field restrictions, before the S₅ and binary-kernel arguments. -/
theorem ordinary_cases_at_two (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c)) (hf : OrdinarySecondFactor c f)
    (hp : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤) :
    (∃ F : BinaryField, IsLinearNatural (secondFactorAction c f) F 2) ∨
    IsSymmetricNatural (secondFactorAction c f) 5 ∨
    IsLinearNatural (secondFactorAction c f) BinaryField.two 3 ∨
    IsRepeatedLinearNatural (secondFactorAction c f) BinaryField.two 3 2 := by
  rcases hf.2 with hn | ⟨F, _, hn⟩
  · cases hn with
    | linearTwo F hn => exact Or.inl ⟨F,hn⟩
    | symmetricFive hn => exact Or.inr (Or.inl hn)
    | linearThree F _ hn =>
      have hF := linearThree_degree_eq_one c he f hp F hn
      obtain ⟨e⟩ := hn
      exact Or.inr (Or.inr (Or.inl ⟨compAction e (degreeOneNaturalEquiv F hF 3)⟩))
  · have hF := doubleThree_degree_eq_one c he f hp F hn
    obtain ⟨e⟩ := hn
    exact Or.inr (Or.inr (Or.inr ⟨compAction e (degreeOneRepeatedEquiv F hF 3 2)⟩))

/-- The literal quotient projection lifts the binary action after its kernel vanishes. -/
theorem binary_secondCase_of_fixed_eq_bot (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤)
    (hn : IsLinearNatural (secondFactorAction c f) BinaryField.two 3 ∨
      IsRepeatedLinearNatural (secondFactorAction c f) BinaryField.two 3 2)
    (hz : Representation.invariants
      ((secondMoved c).toRepresentation.comp (second c).subtype) = ⊥) :
    HyperplaneSecondCase ρ (second c) (secondMoved c) := by
  let q := compAction (fixedQuotientEquiv _ hz) (secondMovedFactorEquiv c he f hm)
  rcases hn with hn | hn
  · obtain ⟨n⟩ := hn
    exact .linearThree 1 (by decide) ⟨compAction (compAction q n) naturalOneEquiv⟩
  · obtain ⟨n⟩ := hn
    exact .linearThree 2 (by decide) ⟨compAction q n⟩

/-- Conditional final assembly. The two additional premises must be proved
from the original FF and nonsplit hypotheses before this is a source theorem. -/
theorem ordinary_secondCase_of_exclusion_and_fixed_kernel (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c)) (hf : OrdinarySecondFactor c f)
    (hp : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤)
    (hfive : ¬ IsSymmetricNatural (secondFactorAction c f) 5)
    (hbinary : (IsLinearNatural (secondFactorAction c f) BinaryField.two 3 ∨
      IsRepeatedLinearNatural (secondFactorAction c f) BinaryField.two 3 2) →
      Representation.invariants ((secondMoved c).toRepresentation.comp (second c).subtype) = ⊥) :
    HyperplaneSecondCase ρ (second c) (secondMoved c) := by
  rcases ordinary_cases_at_two c he f hf hp with ⟨F,hn⟩ | hn | hn | hn
  · exact linearTwo_secondCase c he f hf.1 F hn
  · exact False.elim (hfive hn)
  · exact binary_secondCase_of_fixed_eq_bot c he f hf.1 (Or.inl hn) (hbinary (Or.inl hn))
  · exact binary_secondCase_of_fixed_eq_bot c he f hf.1 (Or.inr hn) (hbinary (Or.inr hn))

/-- The ordinary nonsplit source branch has the precise second action of
B.5.6(5): at most two binary natural SL₃ copies on the actual moved module,
or a natural SL₂ action on its own fixed quotient. The only earlier-source
input is B.4.8(4); the proper-supplement hypothesis is a separate case. -/
theorem ordinary_secondCase_of_nonsplit [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hyp : FFHypothesis K ρ)
    (h48 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    [Nontrivial (second c)]
    (f : FactorModuleConclusion (secondAction c)) (hf : OrdinarySecondFactor c f)
    (hns : ¬ SplitAtSecond c)
    (hproper : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤) :
    HyperplaneSecondCase ρ (second c) (secondMoved c) := by
  exact ordinary_secondCase_of_exclusion_and_fixed_kernel c he f hf hproper
    (not_symmetricFive_of_nonsplit c he f hns)
    (binary_secondMoved_fixed_eq_bot hyp h48 c he f hf.1 hns hproper)

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
