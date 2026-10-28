module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.EqualLinearActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.RecognitionChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction

/-!
# Full marked C₂ recognition from the original equal-linear profile

The actual DGS b=1 actor quotient maps, with their exact original core
kernels, now establish endpoint regularity. The earlier equal-linear
structure theorem supplies the common field, both local PSL₂ markings,
root orders and the commuting root clause. Root reflections and normal
generation are constructed on the same split quotient. The completed
rank-three recognition then gives both orientations of the full Sp₄
amalgam, including Sp₄(2). Its full Borel and both endpoint inclusion
squares are retained by the supplied original amalgam marking.

This removes every extra regularity, reflection, root-size, local-model,
commutator and generation premise from the selected C₂ comparison. The
original b=1 natural actions, their actual actors, the marked split
quotient and the source rotation order four remain earlier inputs.
The Chapter 12 consumer uses its original proper-K/full KnownSimple
preparation to discharge F.1.1.

Source: DGS (10.5), pp.156--157 and Theorem D, p.224;
Fong--Seitz I (6A)(a), II (7C), p.193 and (8A), p.197.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open DGS85.NoncommutingProfile DGS85.Reduction Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The actual DGS actor quotient establishes the endpoint kernel containment. -/
theorem marked_bOne_regularity
    {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (b : Bool)
    (c : BOneActionData (reducedFamily L S) (base (reducedFamily L S) b)
      (base (reducedFamily L S) (!b)) k W)
    (hactor : c.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if b then 1 else 0)).subgroupOf (G₀ L S)) :
    simpleRemainder Q split (if b then 1 else 0) ≤ localKernel Q (if b then 1 else 0) ∧
      (simpleRemainder Q split (if b then 1 else 0)).comap
        (MarkedLocal.endpointMap Q e (if b then 1 else 0)) =
          pCore 2 (parabolic L S (if b then 1 else 0)) := by
  let a := markedBOneActorEquiv Q e h split b c hactor
  exact regularity_of_linear_actor Q e h split (if b then 1 else 0) _
    (subgroupOf_mono _ le_sup_left) (c.quotient.comp a.symm.toMonoidHom)
    (markedBOneActorEquiv_kernel Q e h split b c hactor).le

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
    (base (reducedFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
    (base (reducedFamily L S) false) k₁ W₁)
  (hactor₀ : c₀.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
  (hactor₁ : c₁.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
  (E₀ : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
    W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
include e h split c₀ c₁ hactor₀ hactor₁ E₀

/-- The selected b=1 quadrangle gives the full original symplectic amalgam,
with no independently assumed regularity, local model or root relation. -/
theorem marked_bOne_symplectic_comparison (hm : rotationOrder Q = 4) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam k₀)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam k₀).reverse) := by
  have hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i := by
    intro i
    fin_cases i
    · exact (marked_bOne_regularity Q e h split false c₀ hactor₀).1
    · exact (marked_bOne_regularity Q e h split true c₁ hactor₁).1
  obtain ⟨n,hn,hcard,⟨ν₀⟩,⟨ν₁⟩,hq,_,_⟩ := marked_bOne_sixA Q e h split
    c₀ c₁ hactor₀ hactor₁ E₀ hm (UnitarySource.actorReflection Q split) hV
  let μ : ∀ i, localGroup Q split i ≃* PSL(2,k₀) := Fin.cases ν₀ (fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ν₁)
  exact SymplecticRankThree.comparison_of_linear_row Q e h split hm μ
    (fun i => (hq i).trans hcard.symm)
    (marked_bOne_kernelRoot_commutator Q e h c₀ c₁ split (hV 0))
    (MarkedLocal.unipotentClosure_eq_top_of_source Q e h split)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.NoncommutingProfile ChapterF.Source.DGS85.Reduction
open Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} (D : ChosenModule T L V)
  {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2]
  {k₁ W₀ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
include D

/-- The literal Chapter 12 C₂ row from the earlier DGS natural profile;
all Fong--Seitz local regularity and recognition premises are discharged. -/
theorem rankOne_c2_bOne_source_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (c₀ : BOneActionData (reducedFamily ![L,R] (Global.sourceS L H))
      (base (reducedFamily ![L,R] (Global.sourceS L H)) false)
      (base (reducedFamily ![L,R] (Global.sourceS L H)) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily ![L,R] (Global.sourceS L H))
      (base (reducedFamily ![L,R] (Global.sourceS L H)) true)
      (base (reducedFamily ![L,R] (Global.sourceS L H)) false) k₁ W₁)
    (hactor₀ : c₀.actor = ((B₀ ![L,R] (Global.sourceS L H)).pCoreIn 2 ⊔
      starredParabolic ![L,R] (Global.sourceS L H) 0).subgroupOf (G₀ ![L,R] (Global.sourceS L H)))
    (hactor₁ : c₁.actor = ((B₀ ![L,R] (Global.sourceS L H)).pCoreIn 2 ⊔
      starredParabolic ![L,R] (Global.sourceS L H) 1).subgroupOf (G₀ ![L,R] (Global.sourceS L H)))
    (E₀ : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  let := Fintype.ofFinite k₀
  obtain ⟨m,_,hF⟩ := FiniteField.card k₀ 2
  exact Global.ConcreteAmalgamComparison.symplectic k₀ m m.property
    (by simpa only [Nat.card_eq_fintype_card] using hF)
    (QuadrangleStructure.marked_bOne_symplectic_comparison Q e hf split
      c₀ c₁ hactor₀ hactor₁ E₀ hm)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
