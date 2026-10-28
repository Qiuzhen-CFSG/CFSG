module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Source
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.Reduction

/-!
# The original G.9.2 input to the noncubic Fitting branch

Apply the completed nilpotent-action theorem to the actual Fitting subgroup
and its original binary module. The noncubic commutator makes the sharper
conditional degree bound vacuous. This constructs the marked internal
decomposition needed by G.9.4, with no nilpotent-rigidity callback.

Source: Aschbacher--Smith G.9.2 and G.9.4, printed pp.351--355.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
open Subgroup Theory.GroupTheory
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The genuine earlier theorem for every restriction of the given action. -/
theorem nilpotentRigidityInput (ρ : Representation (ZMod 2) G V) :
    NilpotentRigidityInput ρ :=
  fun _ _ _ h => NilpotentRigidity.source_lemma_G_9_2 h

/-- The actual noncubic source obtains its distinguished four-space and
ordinary factors, with all factor inclusions and actions retained. -/
theorem FiveCore.decomposition_from_source
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}
    (h : FittingHypothesis K ρ A m)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    ∃ H : Subgroup G, A ≤ H ∧ H ≤ fittingSubgroup G ⊔ A ∧
      Nonempty (NilpotentRigidity.ClassifiedDecomposition ρ H True) :=
  FiveCore.decomposition h (nilpotentRigidityInput ρ) hn

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
