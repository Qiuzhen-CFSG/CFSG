module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Complement.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Source

/-!
# The original counterexample supplies the invariant complement

Pair recognition and the original Cartan action place P in L. The source
flag supplies P∩V=V₂, while the completed quotient and shear calculations
give the elementary complement of order q², the literal plane-radical
image and invariance under the original T. The full covering map to SL₃
is retained. Only the preceding source inputs remain explicit, with final
discharge owned by qt-d-1222-shadow-common-core.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs. The exceptional model calculation uses I.2.2(3b).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem source_pair_invariant_complement
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
    ∃ (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)),
      pairCore V H h ≤ L ∧
      axis V H = (SL3.flag D S a).Vi 1 ∧
      pairCore V H h ⊓ V = (SL3.flag D S a).Vi 1 ∧
      Nat.card (pairCore V H h) = (2 ^ S.field.degree) ^ 4 ∧
      (T : Subgroup G) ≤ normalizer (pairCore V H h : Set G) ∧
      (let C := OriginalBlock.pairImage D H h
       let f := OriginalBlock.seedQuotientModel D S a
       Disjoint f.ker C ∧
       OriginalBlock.planeRadicalImage D S a = f.ker ⊔ C ∧
       IsElementaryAbelian 2 C ∧ Nat.card C = (2 ^ S.field.degree) ^ 2 ∧
       C.map (OriginalBlock.alignedSeedModel D S a) =
         (Matrix.PSL3.LinearThree.lineRadicalSL S.field.Carrier).map
           (Matrix.PSL3.LinearThree.lineLocalSL S.field.Carrier).subtype ∧
       (∀ t : T, C.map (OriginalBlock.seedSylowConjugation D S t) = C) ∧
       (∃ Q : Sylow 2 (OriginalBlock.SeedQuotient D),
         (Q : Subgroup (OriginalBlock.SeedQuotient D)) = ((T : Subgroup G).subgroupOf L).map (OriginalBlock.seedProjection D) ∧
         (Q : Subgroup (OriginalBlock.SeedQuotient D)) ≤ normalizer (C : Set (OriginalBlock.SeedQuotient D)))) ∧
      ∃ cover : PerfectCentralCovering.Cover (OriginalBlock.SeedQuotient D)
          (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier),
        cover.toMonoidHom = OriginalBlock.seedQuotientModel D S a := by
  have hAL := hAX.trans (hX.1.trans inf_le_left)
  obtain ⟨a,c,hc2,hI,hK,hcard,hT,hflag⟩ := source_pair_two_summands
    cL flag s p hc hh hm hfixed hf hnot hmodel hG2 R hR cK A hA hHall hAL
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  have hPL := source_pairCore_le_component s hh hz c cK A hA hHall hAL
  obtain ⟨hB,hPV⟩ := hflag (SL3.flag D S a) (SL3.flag_unique D S a)
  obtain ⟨hgen,hLT,hL⟩ := source_pair_core_centralization a (SL3.flag D S a)
    (SL3.flag_inner_unique D S a) s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  have hE := OriginalBlock.pairImage_elementary_card D S s hh hf hk c hc2 hPL
  refine ⟨a,hPL,hB,hPV,hcard,hT,?_,OriginalBlock.seedCover D S a hL,rfl⟩
  exact ⟨OriginalBlock.pairImage_disjoint_kernel D S a s hh hf hk,
    OriginalBlock.planeRadicalImage_eq D S a s hh hf hk c hc2 hB hPL,
    hE.1,hE.2,
    OriginalBlock.pairImage_model_eq_lineRadical D S a s hh hf hk c hc2 hB hPL,
    OriginalBlock.pairImage_sylow_invariant D S hT,
    OriginalBlock.pairImage_sylow_normalizer D hT⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
