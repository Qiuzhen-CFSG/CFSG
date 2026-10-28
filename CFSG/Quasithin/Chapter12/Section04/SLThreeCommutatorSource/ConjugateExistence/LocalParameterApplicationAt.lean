module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleInputs
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalGeometryAt
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassification
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterModels

/-!
# The original conjugator from local source inputs at the same G,T

The Sylow-centralizer bound gives weak closure inside O₂(H). The actual
F.7 geometry and its original subtype maps then give a nontrivial ambient
commutator contained in V intersect its literal conjugate. H-star selection
uses the supplied multiple-overgroup hypothesis. The final conditional
application uses the 12.2.7 sieve to reduce the nonsolvable branch to the
whole-module assertion for a maximal A₅ residual.

The whole moved-module assertion is still owned by qt-d-1241-l3-conjugate;
it is not a claimed consequence of the chosen-action classification. The
same-G,T A₇ exclusion is produced by qt-d-1231-source under Hypothesis1311.
Final symmetric-plane and fusion assembly stays with qt-d-1242-l3-commutator-source.
Source: Aschbacher–Smith, 12.3.2 and 12.4.1, printed pp.807,812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual local parameter yields the original conjugator with the
source Sylow-centralizer bound discharged. -/
theorem noncommutingConjugate_of_hstar_parameter_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    (localModule_sylow_centralizer_eq_core h (structural L h).1 hZ hH).le ha hs
  let A := localGeometryAt h D structural hTH hHM
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hseed : A.seed.map J.subtype = V := localGeometryAt_seed_map h D structural hTH hHM
  have hsyl : ((A.sylow false : Subgroup (localFamily T L H false)).map
      (localFamily T L H false).subtype).map J.subtype = (T : Subgroup G) :=
    localGeometryAt_sylow_map h D structural hTH hHM
  have hsecond : (localFamily T L H true).map J.subtype = H :=
    map_subgroupOf_eq_of_le le_sup_right
  have hw : indexedWeakClosure (A.seed.map J.subtype)
      (((A.sylow false : Subgroup (localFamily T L H false)).map
        (localFamily T L H false).subtype).map J.subtype) 0 ≤
      ((localFamily T L H true).map J.subtype).pCoreIn 2 := by
    rw [hseed,hsyl,hsecond]
    exact hW
  have hc := exists_ambient_conjugate_of_weakClosure_core A
    (localGeometryAt_ne_bot h D structural hTH hHM) J.subtype J.subtype_injective hw
  rwa [hseed] at hc

/-- The actual same-G,T application after the remaining whole A₅-module
assertion. The explicit A₇ premise is used only on genuine overcomponents. -/
theorem noncommutingConjugate_of_maximal_five_modules_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (whole : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
        ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let := D.elementary
  intro hs
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany)
  let := localModule_elementary h hH
  apply noncommutingConjugate_of_hstar_parameter_at h D structural hZ hH _ hs
  by_cases hsolv : Group.IsSolvable H
  · exact localModule_parameter_of_solvable h hH hsolv
  · obtain ⟨hK,hfive,_⟩ := local_residual_maximal_five_of_seven_excluded
      h structural modules hZ hH hsolv seven
    exact localModule_parameter_of_one_or_two h hH (whole H hH hK hfive)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
