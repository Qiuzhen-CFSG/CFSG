module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SourceAssembly
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# The complete B.5.13 dual numerical bound

Strong induction on the order of the nontrivial actor combines all five
adequate B.5 alternatives. The product case restricts the same full module
to a nontrivial factor of strictly smaller order. The other four bounds use
the literal source action, with no extra model or splitting hypothesis.

For a general faithful reduced action whose dual is FF, restriction to its
normal dual-offender subgroup supplies the source hypotheses. The actual
FF witness ensures this subgroup is nontrivial, and the bound transfers
back along its inclusion. Nontriviality in the first statement excludes
the trivial actor admitted by the B.5 hypothesis record.

Source: Aschbacher--Smith B.5.13, printed pp.110--112.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction
universe u v

/-- B.5.13 for the original nontrivial offender-generated dual action. -/
theorem quadraticRatio_le_two_of_source
    {D : Type u} [Group D] [Finite D] [Nontrivial D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis KnownSimple.IsKnownSimple ρ.dual) :
    quadraticRatio ρ ≤ 2 :=
  quadraticRatio_le_two_of_adequateClassification adequateClassification_knownSimple ρ h

/-- The original faithful reduced action inherits the bound from its dual offenders. -/
theorem quadraticRatio_le_two_of_dualFF
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hc : pCore 2 D = ⊥) (c : SQTKQuotient KnownSimple.IsKnownSimple D)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let N := offenderSubgroup ρ.dual
  let : N.Normal := offenderSubgroup_normal ρ.dual
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr
    (offenderSubgroup_ne_bot_of_ff ρ.dual hff)
  have hncore : pCore 2 N = ⊥ := by
    have hle : (pCore 2 N).map N.subtype ≤ pCore 2 D :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
    rw [hc] at hle
    exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp (bot_unique hle)
  have hs : FFHypothesis KnownSimple.IsKnownSimple (Representation.dual (ρ.comp N.subtype)) := {
    finite_module := inferInstance
    faithful := (faithful_dual ρ hf).comp N.subtype_injective
    twoCore := hncore
    generated := offenderSubgroup_restrict_eq_top ρ.dual
    quotient := ⟨c.subgroup N⟩ }
  exact (quadraticRatio_le_of_injective_equivariant (ρ.comp N.subtype) ρ
    N.subtype N.subtype_injective (LinearEquiv.refl _ _) (fun _ _ => rfl)).trans
      (quadraticRatio_le_two_of_source (ρ.comp N.subtype) hs)
end CFSG.Quasithin.ChapterB.SourceB513
