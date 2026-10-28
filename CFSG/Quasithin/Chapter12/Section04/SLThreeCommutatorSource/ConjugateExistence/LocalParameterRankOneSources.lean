module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterSourceExits
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Applying the original rank-one sources to each H-star residual

For the nonsolvable alternative of 12.3.2, the actual residual K = O²(H)
has K/O₂(K) isomorphic to A₅. The projective-line comparison realizes this
same quotient as PSL₂(2²). Structural 12.2.2 supplies a chosen module for K,
and the original H-star member supplies the multiple-overgroup hypothesis.
These are precisely the inputs of the earlier generic and small rank-one
sources. Their exits then feed the checked whole-layer restriction, parameter
bound on all of V_H, and literal ambient conjugator.

The two earlier source implications remain explicit: their producers are
qt-d-1222-rankone-generic and qt-d-1222-rankone-recognition. Only the former's
module/global consequence is used; its exceptional module alternative is not
replaced by an assertion that every outside generation parameter is one.
Final discharge remains with qt-d-1241-l3-conjugate. No assertion of the
unconditional rank-one sources or of universal A₇ exclusion is made here.
Source: Aschbacher–Smith, 5.2.3, 6.2.19–20, 12.3.2 and 12.4.1,
printed pp.649,690–691,807,812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

variable
    (generic : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K → ChosenModule T K W →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ n : ℕ, 1 < n → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) →
      RankOneModule.GenericExit T K)
    (small : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K → ChosenModule T K W →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ n : ℕ, 1 < n → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) →
      RankOneModule.SmallExit T K)

include generic small

/-- Apply both earlier sources to the actual residual, using its own two-core
quotient and a chosen module obtained from the original structural input. -/
theorem local_residual_exits_of_rankOne_sources_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H))
    (hfive : Nonempty
      ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5))) :
    RankOneModule.GenericExit T (localResidual H) ∧
      RankOneModule.SmallExit T (localResidual H) := by
  obtain ⟨⟨W, ⟨D⟩⟩⟩ := (structural _ hK).2.1
  obtain ⟨e⟩ := hfive
  have hfield : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    decide
  have hpsl : ClassicalGroup.IsPSL
      (localResidual H ⧸ pCore 2 (localResidual H)) 2 (2 ^ 2) :=
    ⟨GaloisField 2 2, inferInstance, inferInstance, hfield,
      ⟨e.trans
        (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
          hfield).some.symm⟩⟩
  have hmany := local_hstar_many h structural hH
  exact ⟨generic _ W hK D hmany 2 (by decide) hpsl,
    small _ W hK D hmany 2 (by decide) hpsl⟩

/-- The local 12.3.2 alternatives from the earlier source implications,
without an additional exit premise indexed by the H-star residuals. -/
theorem local_classification_of_rankOne_sources_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7))) :
    Group.IsSolvable H ∨
      (Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
        FaithfulMaximalLocal T (localResidual H) ∧
        Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
          ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H), localResidual H⁆) :=
  local_classification_of_source_exits_at h structural modules hZ hH seven
    (local_residual_exits_of_rankOne_sources_at generic small h structural hH)

/-- The same source implications bound the faithful H-action on the entire
literal omega-span, including the fixed layer and the outer H-action. -/
theorem localModule_parameter_of_rankOne_sources_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    [IsElementaryAbelian 2 (localModule T H)] :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 :=
  localModule_parameter_of_source_exits_at h structural modules hZ hH seven
    (local_residual_exits_of_rankOne_sources_at generic small h structural hH)

/-- Apply the original generic and small source theorems through the local
classification and parameter bound to the literal noncommuting conjugator. -/
theorem noncommutingConjugate_of_rankOne_sources_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7))) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
  noncommutingConjugate_of_source_exits_at h D structural modules hmany hZ seven
    (fun _ hH => local_residual_exits_of_rankOne_sources_at generic small h structural hH)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
