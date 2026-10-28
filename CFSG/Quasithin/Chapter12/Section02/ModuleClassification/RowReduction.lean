module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Multiplicity
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Splitting
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction

/-!
# Exhaustive sum-row reduction on the chosen Irr+ module

The literal central quotient is irreducible. If B.5.1 gives a repeated-natural
or natural-plus-dual moved module, its fixed space vanishes, so that whole
module is irreducible as well. Evaluation excludes multiple copies and
projection excludes the natural-plus-dual row. This concerns D.space; the
independent doubled Sylow-orbit source exclusion is still needed.
Source: Aschbacher--Smith B.5.1(1ii--iv) and 12.2.2, pp.99 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

include c
theorem central_irreducible (s : MovedSection ρ K) :
    IsIrreducible (s.action.comp K.subtype) := by
  apply (irreducible_comp_surjective_iff c.projection c.surjective _).mp
  exact irreducible_of_equiv (actionSymm (c.pulledCentralMarking s))
    D.centralQuotientAction_irreducible

theorem repeated_multiplicity_one (s : MovedSection ρ K)
    (F : BinaryField) {d r : ℕ} (hd : 2 ≤ d) (hr : 0 < r)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural F d) r)) : r = 1 := by
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  have hz := invariants_of_equiv e (repeated_invariants r (linearNatural_invariants F hd))
  let q := movedQuotientEquiv s hz
  have hm := irreducible_of_equiv (actionSymm q) (c.central_irreducible s)
  have hn := irreducible_of_equiv (actionSymm e) hm
  exact ModuleClassification.repeated_length_eq_one _ hr hn

/-- The doubled-three row of B.5.1 is incompatible with this actual Irr+ choice. -/
theorem not_doubleThree (s : MovedSection ρ K) (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural F 3) 2)) : False := by
  have h := c.repeated_multiplicity_one s F (by decide) (by decide) e
  omega

/-- B.5.1's repeated-natural row reduces to a single literal natural marking. -/
theorem repeated_natural_single (s : MovedSection ρ K)
    {d r : ℕ} (hd : d = 4 ∨ d = 5) (hr : 0 < r)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural BinaryField.two d) r)) :
    Nonempty (ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (linearNatural BinaryField.two d)) := by
  have he := c.repeated_multiplicity_one s BinaryField.two (by omega) hr e
  subst r
  let a := ModuleClassification.repeatedOneEquiv (linearNatural BinaryField.two d)
  exact ⟨⟨e.groupEquiv.trans a.groupEquiv,e.linearEquiv.trans a.linearEquiv,fun g v => by
    change a.linearEquiv (e.linearEquiv ((s.space.toRepresentation.comp K.subtype) g v)) = _
    rw [e.intertwines,a.intertwines]
    rfl⟩⟩

/-- The natural-plus-dual row cannot occur on the unchanged chosen Irr+ space.
This does not exclude a doubled Sylow orbit of two different chosen seeds. -/
theorem not_naturalDual (s : MovedSection ρ K) {d : ℕ} (hd : 2 ≤ d)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype) (naturalPlusDual d)) :
    False := by
  have hz := invariants_of_equiv e (naturalDual_invariants hd)
  let q := movedQuotientEquiv s hz
  have hm := irreducible_of_equiv (actionSymm q) (c.central_irreducible s)
  let := irreducible_of_equiv (actionSymm e) hm
  let i : Fin d := ⟨0,by omega⟩
  let f : (naturalPlusDual d).IntertwiningMap (linearNatural BinaryField.two d) :=
    (LinearMap.fst (ZMod 2) (Fin d → ZMod 2) (Module.Dual (ZMod 2) (Fin d → ZMod 2))).intertwiningMap_of_isIntertwiningMap
      _ _ (fun _ _ => rfl)
  have hf : f ≠ 0 := by
    intro he
    have h := congrFun (DFunLike.congr_fun he ((fun _ => 1),0)) i
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) h
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have h := congrArg (fun v => v.2 (fun _ => 1))
    (hinj (show f (0,LinearMap.proj i) = f 0 from rfl))
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) h

/-- Exhaustive B.5.1(1) reduction for the unchanged chosen Irr+ module.
Both reducible sum types are excluded and repeated copies reduce to one. -/
theorem source_irreducible_or_single (b : QuasisimpleSourceConclusion ρ K) :
    IrreducibleAlternative K b.sectionData ∨
      ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (ActionEquiv
        (b.sectionData.space.toRepresentation.comp K.subtype)
        (linearNatural BinaryField.two d)) := by
  cases b.clause_one with
  | irreducible hi hf hr hs he => exact Or.inl ⟨hi,hf,hr,hs,he⟩
  | doubleThree F _ e _ _ => exact (c.not_doubleThree b.sectionData F e).elim
  | naturalDual d hd _ he =>
    obtain ⟨e⟩ := he
    exact (c.not_naturalDual b.sectionData (by omega) e).elim
  | repeatedNatural d r hd hr _ _ he =>
    obtain ⟨e⟩ := he
    exact Or.inr ⟨d,hd,c.repeated_natural_single b.sectionData hd hr e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
