module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalFixedPoint
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Applying nonfaithful residual geometry to the original chosen setup

The maximal and nonfaithful residual assertions in the opening paragraph of
5.1.14 now supply centralization and uniqueness on the original Chapter 12
subgroups. The existing consumer constructs its relative C-component from
these facts. The whole-layer assertion is still a separate source input.

For the chosen-module application, n=2 supplies the actual A₅ marking via
PSL₂(4)'s projective-line action. Residual centralization supplies the outside
centralization premise of the Cartan fixed-point theorem. Chosen T-invariance,
the field parameter and Cartan centralization remain explicit; no conclusion
of 12.2.2 is invoked to prove an earlier source statement.

Source: Aschbacher--Smith, 5.1.14(1--4), 5.1.18--19, pp.638--644.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original multiple-overgroup setup supplies the full reduced input,
and the actual linear-three quotient supplies canonical residual membership.
Neither maximality nor nonfaithfulness is part of this preparation. -/
theorem rankOne_linear_source_preparation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n ∧
      residual H ∈ Chapter1.L G (T : Subgroup G) :=
  ⟨D.rankOne_generic_input_of_many h hmany hn hpsl,
    linear_residual_mem_localFamily hH.1.1 hlinear⟩

/-- The actual exceptional exit, conditional on the two earlier residual
assertions and the independent whole-layer classification. -/
theorem rankOne_exceptional_linear_of_maximal_nonfaithful
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L)) :
    RankOneModule.ExceptionalExit T L H := by
  obtain ⟨hc, hu⟩ := residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hK hnf
  exact D.rankOne_exceptional_linear_of_source hH hlinear hmodel hc hu

/-- The field-four marking is constructed from the original PSL₂ quotient.
The residual geometry discharges outside centralization in the fixed-point
consumer; this conclusion concerns the chosen subgroup only. -/
theorem a5_model_of_linear_source_cartan
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (P : Sylow 2 L) (hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G))
    (C : Subgroup L) (hgen : normalizer (P : Set L) ≤ (P : Subgroup L) ⊔ C)
    (hC : C.map L.subtype ≤ omegaCentralizer T) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hpsl
  have hfour : Nat.card F = 4 := by simpa [hn] using hF
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  have hc := residual_centralizes_omega_of_nonfaithful h.simpleQTKE hH.1.1 hK.1 hnf
  exact D.a5_model_of_outside_cartan_centralization h hH
    ((residual_le_omegaCentralizer_iff hH.1.1.2).mp hc)
    (f.trans a) hTV P hPT C hgen hC

/-- The canonical Borel version needs no selected Sylow or Cartan marking.
The intrinsic Sylow is constructed as T∩L, and the entire Sylow normalizer
fixes the central point used by the earlier fixed-point theorem. -/
theorem a5_model_of_linear_source_borel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hB : localBorel T L ≤ omegaCentralizer T) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow
    T L D.sylow_normalizes_component
  have hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hP, subgroupOf_map_subtype]
    exact inf_le_left
  have hPC : (normalizer (P : Set L)).map L.subtype ≤ omegaCentralizer T := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ _
    rw [hP, ← localBorel_eq_map T L]
    exact hB
  exact D.a5_model_of_linear_source_cartan h hH hK hnf hpsl hn hTV
    P hPT (normalizer (P : Set L)) le_sup_right hPC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
