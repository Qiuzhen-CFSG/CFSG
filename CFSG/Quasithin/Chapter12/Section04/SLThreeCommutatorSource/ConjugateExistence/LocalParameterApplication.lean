module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterMoved
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.Assembly

/-!
# The source centralizer bound in the original conjugator construction

Every generator of W₀(T,V) lies in T. Hence C_T(V_H)=O₂(H) is exactly
the bound required after E.3.10; no bound on all of C_H(V_H) is used.
The original LocalParameterData and conditional APIs are preserved.
This extension proves the solvable H-star branch through the literal
ambient conjugator and reduces the remaining source application to its
nonsolvable H-star parameter calculation.

LocalParameterModels completes the latter calculation for both A₅ alternatives.
The 12.3.2 classification remains an obligation of qt-d-1241-l3-conjugate. The final 12.4.2 owner is
qt-d-1242-l3-commutator-source, which also discharges the original 12.2 inputs.
Source: Aschbacher–Smith 12.2.7(1), 12.3.2 and 12.4.1, pp.797,807,812.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original weak-closure proof only needs the centralizer inside T. -/
theorem weakClosure_le_core_of_sylow_parameter_bound
    (V U H T : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hTH : T ≤ H) (hHN : H ≤ normalizer (U : Set G))
    (hcore : T ⊓ centralizer (U : Set G) ≤ H.pCoreIn 2)
    (ha : moduleA ((automizerRepresentation U).comp (inducedAutomizer U H).subtype) ≤ 1)
    (hs : 1 < globalS V) : indexedWeakClosure V T 0 ≤ H.pCoreIn 2 := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (mem_gamma_zero_iff V T A).mp hA
  exact (le_inf hg (conjugate_centralizes_of_parameter_bound V U H hHN ha hs g
    (hg.trans hTH))).trans hcore

/-- The actual local parameter yields the original conjugator with the
source Sylow-centralizer bound discharged. -/
theorem noncommutingConjugate_of_hstar_parameter
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (localModule T H)]
    (ha : moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1)
    (hs : 1 < globalS V) :
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hHM : ¬ H ≤ normalizer (L : Set G) := hH.1.2
  have hW := weakClosure_le_core_of_sylow_parameter_bound V (localModule T H) H T
    hTH (localModule_normalized T H)
    (localModule_sylow_centralizer_eq_core h (structural G T L h).1 hZ hH).le ha hs
  let A := localGeometry h D structural hTH hHM
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hseed : A.seed.map J.subtype = V := localGeometry_seed_map h D structural hTH hHM
  have hsyl : ((A.sylow false : Subgroup (localFamily T L H false)).map
      (localFamily T L H false).subtype).map J.subtype = (T : Subgroup G) :=
    localGeometry_sylow_map h D structural hTH hHM
  have hsecond : (localFamily T L H true).map J.subtype = H :=
    map_subgroupOf_eq_of_le le_sup_right
  have hw : indexedWeakClosure (A.seed.map J.subtype)
      (((A.sylow false : Subgroup (localFamily T L H false)).map
        (localFamily T L H false).subtype).map J.subtype) 0 ≤
      ((localFamily T L H true).map J.subtype).pCoreIn 2 := by
    rw [hseed,hsyl,hsecond]
    exact hW
  have hc := exists_ambient_conjugate_of_weakClosure_core A
    (localGeometry_ne_bot h D structural hTH hHM) J.subtype J.subtype_injective hw
  rwa [hseed] at hc

/-- The solvable local branch is now complete through the literal conjugator. -/
theorem noncommutingConjugate_of_solvable_hstar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsolv : Group.IsSolvable H) [IsElementaryAbelian 2 V] (hs : 1 < globalS V) :
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let := localModule_elementary h hH
  exact noncommutingConjugate_of_hstar_parameter h D structural hZ hH
    (localModule_parameter_of_solvable h hH hsolv) hs

/-- The actual single-module alternative of 12.3.2 reaches the requested
ambient conjugator, retaining K/O₂(K) and the original V_K section. -/
theorem noncommutingConjugate_of_source_single_hstar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (q : (localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection (localResidual H)
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆ ⊥
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localResidual H))))))
    [IsElementaryAbelian 2 V] (hs : 1 < globalS V) :
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let := localModule_elementary h hH
  exact noncommutingConjugate_of_hstar_parameter h D structural hZ hH
    (localModule_parameter_of_source_single h hH q c) hs

/-- Only the nonsolvable branch of the original parameter argument remains.
This is an explicit obligation, not an established source classification. -/
def NonsolvableLocalParameterSource : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) → ChosenModule T L V →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    centralizer (sylowCenterSeed T : Set X) ≤ normalizer (L : Set X) →
    ∀ H : Subgroup X, (hH : H ∈ Chapter3.HStar (T : Subgroup X) (normalizer (L : Set X))) →
      ¬ Group.IsSolvable H → letI := localModule_elementary h hH
        moduleA ((automizerRepresentation (localModule T H)).comp
          (inducedAutomizer (localModule T H) H).subtype) ≤ 1

/-- Original 12.4.1 reduced to the nonsolvable parameter calculation. The
whole solvable branch is discharged. SelectionSource.localSelectionSource
supplies the selection argument from structural and marked 12.2.2. -/
theorem noncommutingConjugate1241_of_nonsolvable_parameters
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (selection : LocalSelectionSource.{u})
    (parameters : NonsolvableLocalParameterSource.{u}) : NoncommutingConjugate1241.{u} := by
  intro X _ _ T L V h D hmodel hne hZ
  let := D.elementary
  intro hs
  obtain ⟨H,hH⟩ := selection X T L V h D hmodel hne hZ hs
  let := localModule_elementary h hH
  apply noncommutingConjugate_of_hstar_parameter h D structural hZ hH _ hs
  by_cases hsolv : Group.IsSolvable H
  · exact localModule_parameter_of_solvable h hH hsolv
  · exact parameters X T L V h D hmodel hne hZ H hH hsolv

/-- The original symmetric-plane consumer of the remaining nonsolvable input. -/
theorem source_commutator_plane_of_nonsolvable_parameters
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u}) (centralizers : HyperplaneCentralizers1248.{u})
    (selection : LocalSelectionSource.{u})
    (parameters : NonsolvableLocalParameterSource.{u})
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction centralizers
    (noncommutingConjugate1241_of_nonsolvable_parameters structural selection parameters)
    T L V h D hmodel hne
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
