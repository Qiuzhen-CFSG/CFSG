module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterRestriction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterApplicationAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModule

/-!
# The whole-layer source exits applied to the literal local omega module

Reducedness places U=⟨Ω₁Z(T)ᴴ⟩ in R₂(KT), where K=O²(H) and KT=H.
Restrict the marked one-or-two-copy model of [R₂(KT),K] to [U,K]. The
source centralizer guard makes this restriction nonzero. This completes
the local restriction, classification-to-parameter implication and ambient
noncommuting-conjugator application without any moved-module callback.

The genuine earlier generic and small exits of 6.2.20 remain with
qt-d-1222-rankone-module; the same-G,T A₇ exclusion remains with
qt-d-1231-source and retains Hypothesis1311 in its D application. This
conditional extension does not prove those inputs or the stronger legacy
whole-H centralizer field. Final source assembly remains with
qt-d-1241-l3-conjugate and qt-d-1242-l3-commutator-source.
Source: Aschbacher–Smith, 12.2.7(3i), 12.3.2 and 12.4.1, pp.797,807,812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal omega-span belongs to the entire reduced module of KT=H. -/
theorem localModule_le_wholeReduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    localModule T H ≤ RankOneModule.wholeReduced T (localResidual H) := by
  change localModule T H ≤ (ReducedModule (localResidual H ⊔ (T : Subgroup G))).map _
  rw [localResidual_supplement hH.1.1.2]
  rw [←map_subgroupOf_eq_of_le (localModule_le hH.1.1.2)]
  exact map_mono (localModule_reduced h hH).le_reducedPSubgroup

/-- Restrict the actual whole-layer model to the nonzero moved omega-span. -/
theorem localMoved_one_or_two_of_wholeReduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
      (RankOneModule.commutatorLayer T (localResidual H))) :
    Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆ := by
  let := localModule_elementary h hH
  let : IsElementaryAbelian 2 (localMoved T H) := IsElementaryAbelian.of_le (localMoved_le T H)
  have hm' := hm.of_le (commutator_mono (localModule_le_wholeReduced h hH) le_rfl)
    ((map_subtype_le (pResidual 2 H)).trans (localMoved_normalized T H))
    (localMoved_ne_bot hTM hZ hH)
  simpa only [localMoved,localModule_eq_residual_span hH.1.1.2] using hm'

/-- The earlier generic and small source exits suffice for the local module
clause, with no unexplained decomposition of the omega-span. -/
theorem localMoved_one_or_two_of_source_exits
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H))
    (generic : RankOneModule.GenericExit T (localResidual H))
    (small : RankOneModule.SmallExit T (localResidual H)) :
    Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆ := by
  obtain ⟨⟨W,⟨D⟩⟩⟩ := (structural _ hK).2.1
  exact localMoved_one_or_two_of_wholeReduced h (structural L h).1 hZ hH
    (D.rankOne_layer_of_source_exits_of_many hK (local_hstar_many h structural hH) generic small)

/-- Source 12.3.2 at the original G,T, retaining exactly the earlier A₇ and
6.2.20 source obligations. Both residual two-core and maximal faithfulness
are the original ones. -/
theorem local_classification_of_source_exits_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    Group.IsSolvable H ∨
      (Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
        FaithfulMaximalLocal T (localResidual H) ∧
        Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
          ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆) := by
  by_cases hs : Group.IsSolvable H
  · exact Or.inl hs
  · obtain ⟨hK,hfive,_⟩ := local_residual_maximal_five_of_seven_excluded
      h structural modules hZ hH hs seven
    have hx := exits hK hfive
    exact Or.inr ⟨hfive,hK.maximal_faithful,
      localMoved_one_or_two_of_source_exits h structural hZ hH hK hx.1 hx.2⟩

/-- The original source alternatives bound the automizer action on all of U,
including its fixed layer and every outer H-actor. -/
theorem localModule_parameter_of_source_exits_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    [IsElementaryAbelian 2 (localModule T H)] :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  rcases local_classification_of_source_exits_at h structural modules hZ hH seven exits with
    hs | ⟨_,_,hm⟩
  · exact localModule_parameter_of_solvable h hH hs
  · exact localModule_parameter_of_one_or_two h hH hm

/-- The earlier source exits feed the literal noncommuting conjugator, with
selection, restriction, outer actions and fixed layers all discharged here. -/
theorem noncommutingConjugate_of_source_exits_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let := D.elementary
  intro hs
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany)
  let := localModule_elementary h hH
  exact noncommutingConjugate_of_hstar_parameter_at h D structural hZ hH
    (localModule_parameter_of_source_exits_at h structural modules hZ hH seven (exits H hH)) hs
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
