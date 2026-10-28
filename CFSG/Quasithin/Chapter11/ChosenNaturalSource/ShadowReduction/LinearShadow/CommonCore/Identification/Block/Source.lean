module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Centralization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Cover

/-!
# The common-pair counterexample yields the original SL₃ block

The proved pair recognition selects the actual SL₃ action. Its canonical
flag and the given original Cartan action construct V_K, and the FSU
commutator calculation gives [O₂(L),L]=V. The block model and perfect
central covering map therefore apply without any extra local premise.
The conclusion keeps the field-four alternative for the remaining literal
Sylow-invariant complement argument.

Only the preceding 11.3.7 action and earlier source inputs remain explicit;
qt-d-1222-shadow-common-core owns their final discharge. The complement
exclusion and final local-core recovery stay with this identification task.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774, paragraphs 1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

/-- The original counterexample constructs the full SL₃ block and its literal
cover, with the field-four core alternative retained. The remaining invariant
complement exclusion and final local core equalities belong to this task. -/
theorem source_pair_sl3_block_and_cover
    (cL : Coordinates D S.field) (flag : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    L = ⁅L,pairNaturalSpan T V H h⁆ ∧
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V ∧
      ⁅L.pCoreIn 2,L⁆ = V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree ∧
      (ChapterC.blockU L).map L.subtype = V ∧
      ∃ a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
        (∃ c : PerfectCentralCovering.Cover (OriginalBlock.SeedQuotient D)
            (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier),
          ∀ l : L, c.toMonoidHom (OriginalBlock.seedProjection D l) =
            a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∧
        ((L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V) ∨
          (2 ^ S.field.degree = 4 ∧ pCore 2 (OriginalBlock.SeedQuotient D) ≠ ⊥)) := by
  have hAL := hAX.trans (hX.1.trans inf_le_left)
  obtain ⟨a,c,hmult,hcore,hres,hcard,hT,hflag⟩ := source_pair_two_summands
    cL flag s p hc hh hm hfixed hf hnot hmodel hG2 R hR cK A hA hHall hAL
  obtain ⟨hgen,hLT,hL⟩ := source_pair_core_centralization a (SL3.flag D S a)
    (SL3.flag_inner_unique D S a) s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  exact ⟨hgen,hLT,hL,OriginalBlock.component_sl3_block D S a hL,
    OriginalBlock.blockU_map hL,a,
    ⟨OriginalBlock.seedCover D S a hL,OriginalBlock.seedCover_mk D S a hL⟩,
    OriginalBlock.core_alternative D S a hL⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
