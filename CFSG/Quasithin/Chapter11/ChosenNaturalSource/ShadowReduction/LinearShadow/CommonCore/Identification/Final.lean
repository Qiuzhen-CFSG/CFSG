module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.LocalCore

/-!
# Final common-core identities for the original counterexample

The preceding source inputs construct the pair, its elementary natural
action, the original SL₃ block and full covering map. The invariant-complement
argument recovers V=O₂(L)=C_L(V), retaining q=4. The Thompson and scalar-plane
arguments finish P=J(PV)=O₂(L₂)=O₂(K)=O₂(I), with the same original conjugator,
flag and quotient maps. No local recognition or core equality is assumed.

Only the explicitly displayed earlier 11.3.7 and local-geometry inputs remain;
qt-d-1222-shadow-common-core owns their final discharge through the existing
common-action, parameter-component and natural-local-geometry producers.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem source_pair_final_core_identifications
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
    L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V ∧
      ∃ a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
        ChapterC.IsSL3EvenBlock L S.field.degree ∧
        axis V H = (SL3.flag D S a).Vi 1 ∧
        pairCore V H h ⊓ V = (SL3.flag D S a).Vi 1 ∧
        IsElementaryAbelian 2 (pairCore V H h) ∧
        Nat.card (pairCore V H h) = (2 ^ S.field.degree)^4 ∧
        (SL3.flag D S a).Ri 1 ⊓ L = pairCore V H h ⊔ V ∧
        Stellmacher.elementaryAbelianMaxJ (pairCore V H h ⊔ V) = pairCore V H h ∧
        pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
        pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
        pairCore V H h = ((SL3.flag D S a).Li 1).pCoreIn 2 ∧
        (∃ cover : PerfectCentralCovering.Cover (OriginalBlock.SeedQuotient D)
            (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier),
          cover.toMonoidHom = OriginalBlock.seedQuotientModel D S a) := by
  obtain ⟨hLV,hcent,a,hB,hPV,hcard,hRad,hJ,him,hnJ,hnC⟩ :=
    source_pair_thompson_and_normalizers cL flag s p hc hh hm hfixed hf hnot hmodel hG2
      R hR cK A X hA hHall hX hAX
  have hPL : pairCore V H h ≤ L :=
    (le_sup_left.trans hRad.symm.le).trans inf_le_right
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  obtain ⟨hI,⟨c⟩⟩ := source_pair_recognition s hh hm hf hnot hmodel cK R hR
    A hA hHall (hAX.trans (hX.1.trans inf_le_left))
  have hK := pairCore_eq_residual_core_of_moved s hh hk hI c.commutator_eq
  have hL2 := CoreRecovery.pair_eq_local_core D S a (pairCore V H h) hPL hLV hPV hRad hJ him
  obtain ⟨hgen,hLT,hL⟩ := source_pair_core_centralization a (SL3.flag D S a)
    (SL3.flag_inner_unique D S a) s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  exact ⟨hLV,hcent,a,OriginalBlock.component_sl3_block D S a hL,hB,hPV,
    pairCore_elementary s hh hz,hcard,hRad,hJ,hI,hK,hL2,
    OriginalBlock.seedCover D S a hL,rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
