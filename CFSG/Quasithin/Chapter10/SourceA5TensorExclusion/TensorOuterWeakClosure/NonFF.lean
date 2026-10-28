module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFusionSource
public import CFSG.Quasithin.Chapter10.SourceWeakClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport

/-!
# The tensor module is non-FF for its full ambient automizer

The full-module normalizer is the actual maximal local subgroup. Hence the
proved non-FF action-image theorem applies to the entire normalizer, not only
the component subgroup. This discharges the automizer premise of E.3.11 in
the initial zero-corank weak-closure argument of Aschbacher–Smith 9.4.4,
printed p.736, before its use in the corank-one argument 9.4.5.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original tensor module is non-FF for its full ambient automizer. -/
theorem fullModule_automizer_notFF :
    let := m.fullModule_elementary
    ¬ IsFFModule (automizerRepresentation D.fullModule) := by
  let := m.fullModule_elementary
  have hL : localOrbit T L ≤ normalizer (D.fullModule : Set G) :=
    (localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule
  have hN : normalizer (D.fullModule : Set G) ≤ normalizer (localOrbit T L : Set G) := by
    rw [source_fullModule_normalizer D]
  have h := m.fullModule_actionImage_notFF (normalizer (D.fullModule : Set G)) hL hN le_rfl
  exact h

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
