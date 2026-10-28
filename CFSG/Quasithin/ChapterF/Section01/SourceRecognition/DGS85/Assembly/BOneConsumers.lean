module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.C2Consumers

/-!
# The complete b=1 profile branch in the original Chapter 12 pair

The reduced natural profile selects its linear or symplectic comparison
without an assumed rotation order or centerfree actor. Native restoration
then gives the full original comparison. The actual original quotient
markings recover the input field degree and both natural blocks, while the
normalized right Borel gives the original right-core equality and S≤R.
No equality of original and reduced Sylows is assumed.

The literal Chapter 12 application retains its original proper-K and full
KnownSimple hypotheses, arbitrary prepared perfect selected R and the
original S. The whole-residual specialization feeds GlobalExit. The natural
profile and apartment/split inputs remain with the earlier source producers;
this proves their b=1 conditional assembly, not full DGS exhaustiveness.

Source: DGS (1985), (10.5), Theorem D and (15.2), pp.156,224,226--228;
Aschbacher--Smith F.1.12, 5.2.6 and 12.2.2, pp.263--264,650--651,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
open OriginalExtension FongSeitzBinary
variable {G X W₀ W₁ : Type*} {k₀ k₁ : Type} [Group G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {L R S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual reduced natural profile supplies its row of the broad catalogue. -/
theorem reduced_alternatives (h : HypothesisF11 ![L,R] S)
    (p : C2Source.Profile ![L,R] S k₀ k₁ W₀ W₁)
    (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam ![L,R] S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives L R S := by
  rcases reduced_comparison h p E₁ Q e split with ⟨_,point,he⟩ | ⟨hm,_⟩
  · let := Fintype.ofFinite k₁
    obtain ⟨m,_,hF⟩ := FiniteField.card k₁ 2
    exact .linear k₁ m m.property (by simpa only [Nat.card_eq_fintype_card] using hF) point he
  · exact C2Source.reduced_alternative h p Q e split hm

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
open ChapterF.Source.DGS85.OriginalExtension
variable {G X W₀ W₁ : Type*} {k₀ k₁ : Type} [Group G] [Finite G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Restore the selected A₂ or C₂ row on the original pair, with field, blocks and core. -/
theorem comparison_and_core_of_reduced_bOne
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (p : C2Source.Profile ![L,R] (sourceS L H) k₀ k₁ W₀ W₁)
    (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      Nat.card k₀ = 2^n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  let hf := d.hypothesisF11 h hTH
  rcases BOneSource.reduced_comparison hf p E₁ Q e split with ⟨_,point,⟨f⟩⟩ | ⟨hm,_⟩
  · let := Fintype.ofFinite k₁
    obtain ⟨m,_,hF⟩ := FiniteField.card k₁ 2
    have hcard : Nat.card k₁ = 2^(m : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hF
    have hm := d.linear_reduced_parameter h hTH hp k₁ m.property hcard point f
    have hc := d.originalLinearComparisonOfReduced h hTH hp k₁ m.property hcard point f
    have he : Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam k₁)) ∨
        Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
          (ChapterF.GreenBook.LieModels.LinearThree.amalgam k₁).reverse) := by
      cases point
      · exact Or.inl ⟨hc⟩
      · exact Or.inr ⟨hc⟩
    obtain ⟨hmn,hL,hR⟩ := d.linear_amalgam_blocks h hTH hp k₁ m.property hcard he
    have hfield := NoncommutingProfile.paired_field_orders_eq
      (Reduction.reduced_triple hf) p.left p.right p.natural
    exact ⟨.linear k₁ m m.property hcard he,
      hfield.trans (hcard.trans (congrArg (fun z => 2^z) hmn)), hL,hR,
      linear_original_core_and_containment_of_reduced_iso d h hTH k₁ hm hcard point f hp⟩
  · exact d.comparison_and_core_of_reduced_bOne_quadrangle h hTH hp p Q e split hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.Assembly ChapterF.Source.DGS85.OriginalExtension
variable {G X W₀ W₁ : Type*} {k₀ k₁ : Type} [Group G] [Finite G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (p : C2Source.Profile ![L,R] (Global.sourceS L H) k₀ k₁ W₀ W₁)
  (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
    W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)

include D h hmany hn hpsl hH d hp p E₁ e split in
/-- Apply the derived b=1 alternative to the literal Chapter 12 preparation. -/
theorem rankOne_comparison_and_core_of_reduced_bOne :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      Nat.card k₀ = 2^n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_reduced_bOne
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp p E₁ Q e split

omit d hp p e in
include D h hmany hn hpsl hH E₁ split in
/-- The whole-residual preparation gives GlobalExit from the constructed comparison. -/
theorem rankOne_globalExit_of_reduced_bOne
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (p : C2Source.Profile ![L,residual H] (Global.sourceS L H) k₀ k₁ W₀ W₁)
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_and_core_of_reduced_bOne
      h hmany hn hpsl hH d hp p E₁ Q e split).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
