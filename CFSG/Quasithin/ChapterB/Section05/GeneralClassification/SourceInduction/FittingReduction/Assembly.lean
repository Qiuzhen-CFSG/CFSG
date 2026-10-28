module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.ActionTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.FirstFactor
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.ModuleTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.FixedQuotientSum

/-!
# The induction and module assembly after selecting the S₃ factor

Classify only the actual second subgroup on its fixed complement, whose
strictly smaller order and every B.5.3 hypothesis have been proved. Apply the
intermediate rank-one extraction to that action. The included submodule and
its quotient intertwiner then construct every B.5.6(3) clause, including the
four-dimensional indecomposable alternative, on V/C_V(G).

The B.1.9 selection and the SQTK-cover rank estimate are separate missing
inputs to B.5.8's final assembly. Neither is asserted by this module.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.8, p.106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
universe u v

private def composeAction {D E H U W X : Type*} [Group D] [Group E] [Group H]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) E W}
    {π : Representation (ZMod 2) H X} (e : ActionEquiv σ τ) (f : ActionEquiv τ π) :
    ActionEquiv σ π :=
  ⟨e.groupEquiv.trans f.groupEquiv,e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

private theorem factorNatural_transport {D E U W : Type*} [Group D] [Group E]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) E W}
    (e : ActionEquiv σ τ) (h : FactorNatural τ) : FactorNatural σ := by
  cases h with
  | linearTwo F h => exact .linearTwo F ⟨composeAction e h.some⟩
  | symmetricFive h => exact .symmetricFive ⟨composeAction e h.some⟩
  | linearThree F ho h => exact .linearThree F ho ⟨composeAction e h.some⟩

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G} (c : Configuration ρ A)

/-- All three factor cases pass through the original inclusion and quotient.
The exceptional case transports the full record, without a new source premise. -/
theorem Configuration.lift_factorCase (f : FactorModuleConclusion c.secondAction) :
    SourceFactorCase ρ c.second (c.liftSpace f.space) := by
  let e := actionSymm (c.factorImageEquiv f.space)
  have hm (h : f.space.toSubmodule = moved c.secondAction ⊤) :
      (c.liftSpace f.space).toSubmodule = moved ρ c.second := by
    change f.space.toSubmodule.map c.secondSpace.toSubmodule.subtype = _
    rw [h,c.map_second_moved]
  cases f.actionCase with
  | natural h hn => exact .natural (hm h) (factorNatural_transport e hn)
  | doubleNatural F ho h hn =>
      exact .doubleNatural F ho (hm h) ⟨composeAction e hn.some⟩
  | exceptional h q =>
      have hh := Submodule.map_mono (f := c.secondSpace.toSubmodule.subtype) h
      rw [c.map_second_moved] at hh
      exact .exceptional hh (fourDimensional_transport e q).some

/-- The constructed two-factor case decomposes the literal global fixed
quotient and retains the original subgroup inclusions. -/
noncomputable def Configuration.twoFactor [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (f : FactorModuleConclusion c.secondAction) :
    SourceTwoFactorCase ρ :=
  SourceTwoFactorCase.of_cross_fixed_mod_fixed ρ c.product c.firstSpace (c.liftSpace f.space)
    (by rw [sup_assoc,c.lift_supplement]; exact c.decomposition.sup_eq_top)
    c.cross_fixed ((c.liftSpace_le f.space).trans c.secondSpace_eq.le)
    (c.firstCase ρ hf) (c.lift_factorCase f)

/-- The full B.5.8 contradiction after selection and the cover-rank bound.
The extraction hypothesis is the explicit intermediate contract whose
producer is qt-b05-induction-factor-extraction; it is not an earlier theorem. -/
theorem Configuration.adequate [Finite G] {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (ih : SmallerClassification.{u,v} K (Nat.card G))
    (extract : RankOneModuleExtraction.{u,v} K) (hr : primeRank 3 c.second ≤ 1) :
    AdequateAlternative ρ := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  by_cases hz : c.second = ⊥
  · exact Or.inr (.symmetricThree (c.symmetricThree hz))
  · let : Nontrivial c.second := (Subgroup.nontrivial_iff_ne_bot c.second).mpr hz
    obtain ⟨f⟩ := extract c.second c.secondSpace.toSubmodule c.secondAction
      (c.descent hyp).2 hr (c.classify_second hyp ih)
    exact Or.inr (.twoFactors (c.twoFactor hyp.faithful f))

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
