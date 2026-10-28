module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Folding
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootGeneration
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The two marked root-word evaluations for F4 folding

The source uses the existing F4 root pairing and its literal central
projection. The target uses `f4Simple`, hence the reversal of E6 orbit
labels proved in `foldedCartan_f4`. Both evaluations are surjective by
signed simple-root generation. A source word is trivial exactly when its
cover value is central, not merely when that matrix is the identity.

These definitions fix the common word domain for the independent matrix
comparison arguments. No cross-representation word relation is asserted.
Sources: GLS3 §§2.2--2.6 and Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance wordsRootFintype : Fintype typeF4Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- The literal F4 matrix group before its full-center quotient. -/
abbrev Cover := ExceptionalSplit.rootGenerated typeF4RootPairing typeF4RootPairing_base F
abbrev sourceIndex (i : Fin 4) := typeF4RootPairing_baseEquiv i

/-- The source simple root in the standard F4 numbering, with either sign. -/
def coverSimple (s : Bool) (i : Fin 4) (t : F) : Cover F :=
  let := typeF4RootPairing.indexNeg
  if s then ExceptionalSplit.elementaryRoot _ _ F (sourceIndex i) t
  else ExceptionalSplit.elementaryRoot _ _ F (-(sourceIndex i) : typeF4Roots) t

/-- The projected source curve whose image the folding identification must preserve. -/
def sourceSimple (s : Bool) (i : Fin 4) (t : F) : ExceptionalSplit.F4 F :=
  ExceptionalSplit.projection _ _ F (coverSimple F s i t)

@[simp] theorem coverSimple_val (s : Bool) (i : Fin 4) (t : F) :
    (coverSimple F s i t).val =
      (RootPairing.SimpleGeckGroup.simpleFamily (b := typeF4RootPairing_base)).unit
        (s, sourceIndex i) t := by
  let := typeF4RootPairing.indexNeg
  cases s
  · exact rootCurveUnit_neg_simple (sourceIndex i) t
  · exact rootCurveUnit_simple (sourceIndex i) t

/-- Both signed numbered curves generate the actual F4 matrix cover. -/
theorem coverSimple_generates (H : Subgroup (Cover F))
    (h : ∀ s i t, coverSimple F s i t ∈ H) : H = ⊤ := by
  let := typeF4RootPairing.indexNeg
  apply ExceptionalSplit.elementary_subgroup_eq_top_of_simple
  · intro i t
    simpa [coverSimple, sourceIndex] using h true (typeF4RootPairing_baseEquiv.symm i) t
  · dsimp only
    intro i t
    simpa [coverSimple, sourceIndex] using h false (typeF4RootPairing_baseEquiv.symm i) t

/-- Reversing the four orbit labels preserves generation of the folded subgroup. -/
theorem f4Simple_generates (H : Subgroup (splitSubgroup F))
    (h : ∀ s i t, f4Simple F s i t ∈ H) : H = ⊤ := by
  have hle : splitSubgroup F ≤ H.map (splitSubgroup F).subtype := by
    change Subgroup.closure (Set.range fun x : Bool × Fin 4 × F =>
      foldedSimple F x.1 x.2.1 x.2.2) ≤ H.map (splitSubgroup F).subtype
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    refine ⟨f4Simple F s i.rev t, h s i.rev t, ?_⟩
    simp [f4Simple]
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

/-- Formal words on precisely the eight parameterized signed simple-root curves. -/
abbrev Word := FreeGroup (Bool × Fin 4 × F)

def coverEvaluation : Word F →* Cover F :=
  FreeGroup.lift fun x => coverSimple F x.1 x.2.1 x.2.2

def sourceEvaluation : Word F →* ExceptionalSplit.F4 F :=
  (ExceptionalSplit.projection _ _ F).comp (coverEvaluation F)

def foldedEvaluation : Word F →* splitSubgroup F :=
  FreeGroup.lift fun x => f4Simple F x.1 x.2.1 x.2.2

@[simp] theorem coverEvaluation_of (s : Bool) (i : Fin 4) (t : F) :
    coverEvaluation F (FreeGroup.of (s, i, t)) = coverSimple F s i t :=
  FreeGroup.lift_apply_of

@[simp] theorem sourceEvaluation_of (s : Bool) (i : Fin 4) (t : F) :
    sourceEvaluation F (FreeGroup.of (s, i, t)) = sourceSimple F s i t := by
  simp [sourceEvaluation, sourceSimple]

@[simp] theorem foldedEvaluation_of (s : Bool) (i : Fin 4) (t : F) :
    foldedEvaluation F (FreeGroup.of (s, i, t)) = f4Simple F s i t :=
  FreeGroup.lift_apply_of

theorem coverEvaluation_surjective : Function.Surjective (coverEvaluation F) := by
  rw [← MonoidHom.range_eq_top]
  apply coverSimple_generates
  intro s i t
  exact ⟨FreeGroup.of (s, i, t), coverEvaluation_of F s i t⟩

theorem sourceEvaluation_surjective : Function.Surjective (sourceEvaluation F) :=
  (ExceptionalSplit.projection_surjective _ _ F).comp (coverEvaluation_surjective F)

theorem foldedEvaluation_surjective : Function.Surjective (foldedEvaluation F) := by
  rw [← MonoidHom.range_eq_top]
  apply f4Simple_generates
  intro s i t
  exact ⟨FreeGroup.of (s, i, t), foldedEvaluation_of F s i t⟩

@[simp] theorem sourceEvaluation_eq_one_iff (w : Word F) :
    sourceEvaluation F w = 1 ↔ coverEvaluation F w ∈ Subgroup.center (Cover F) :=
  ExceptionalSplit.projection_eq_one_iff _ _ F _

end TwistedE6.FoldedSubsystem.F4Identification
