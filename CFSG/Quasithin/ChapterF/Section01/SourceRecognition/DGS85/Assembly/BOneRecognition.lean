module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNative

/-!
# Both regular models from the b=1 source profile

The order comparison selects A₂ or C₂ on the same independently marked
split quotient. In the triangular branch it also supplies the actual actor
centerfreeness. Transport the original reduced actions to the full family
on S₀, then apply the proved marked A₂ recognition. The other branch uses
the proved C₂ recognition and reduction idempotence. Both orientations,
both endpoint inclusion squares and the whole reduced Borel are retained,
including fields two and four.

Only the two natural actions, their literal actors, the natural module
markings and the marked split quotient are inputs. Neither row selection
nor a model comparison is assumed. Construction of those earlier inputs
and the other source branches remain obligations of source assembly.

Source: DGS, Groups and Graphs (1985), (10.5) and Theorem D,
printed pp.156--157,224; Fong--Seitz I (6A)(a), II (7C),(8A).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
open SuzukiContainment Reduction NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open OriginalExtension FongSeitzBinary
variable {G X k₀ k₁ W₀ W₁ : Type*} [Group G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

private theorem reduced_linear_comparison (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 3)
    (hc : centerIn p.right.actor = ⊥) :
    ∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam k₁ point)) := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.left.actor : Set _) := by
    rw [p.left_actor]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.right.actor : Set _) := by
    rw [p.right_actor]
    exact reduced_borel_normalizes_source_actor h 1
  have hd₀ : ∃ (a₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
      (a₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
        (base (reducedFamily L S) false) k₁ W₁),
      (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (a₀.actor : Set _) ∧
      (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (a₁.actor : Set _) ∧ centerIn a₁.actor = ⊥ :=
    ⟨p.left,p.right,hn₀,hn₁,hc⟩
  have hd : ∃ (a₀ : BOneActionData (fullFamily L (reducedSylow L S))
      (base (fullFamily L (reducedSylow L S)) false)
      (base (fullFamily L (reducedSylow L S)) true) k₀ W₀)
      (a₁ : BOneActionData (fullFamily L (reducedSylow L S))
      (base (fullFamily L (reducedSylow L S)) true)
      (base (fullFamily L (reducedSylow L S)) false) k₁ W₁),
      (commonBorel L (reducedSylow L S)).subgroupOf (generated L (reducedSylow L S)) ≤
        normalizer (a₀.actor : Set _) ∧
      (commonBorel L (reducedSylow L S)).subgroupOf (generated L (reducedSylow L S)) ≤
        normalizer (a₁.actor : Set _) ∧ centerIn a₁.actor = ⊥ := by
    unfold fullFamily
    rw [←G₀_eq_source h]
    have hF : (fun i => (P₀ L S i).subgroupOf (G₀ L S)) =
        (fun i => (parabolic L (reducedSylow L S) i).subgroupOf (G₀ L S)) := by
      funext i
      rw [P₀_eq_source h i]
    rw [←hF]
    simpa only [reducedFamily,B₀_eq_source h] using hd₀
  obtain ⟨a₀,a₁,ha₀,ha₁,hac⟩ := hd
  let hr := reduced_hypothesis h
  let j := A2Source.intersectionAmalgamIso hr
  have he : ∃ i : Fin 2, Nonempty (Iso (reducedAmalgam L S)
      (Matrix.PSL3.RootPresentationRecognition.flagAmalgam k₁ i)) :=
    ⟨_,⟨j.symm.trans (A2Source.MarkedRecognition.comparison Q (intersectionMark h Q e) hr
      a₀ a₁ ha₀ ha₁ p.natural E₁ hm hac split)⟩⟩
  obtain ⟨i,⟨f⟩⟩ := he
  fin_cases i
  · exact ⟨false,⟨f⟩⟩
  · exact ⟨true,⟨f⟩⟩

/-- Exhaust the two b=1 models, deriving their Weyl orders and triangular centerfreeness. -/
theorem reduced_comparison (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (rotationOrder Q = 3 ∧ ∃ point : Bool,
      Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam k₁ point))) ∨
    (rotationOrder Q = 4 ∧ ∃ point : Bool,
      Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam k₀ point))) := by
  rcases rotation_and_center h p E₁ Q e split with ⟨hm,_,hc⟩ | hm
  · exact Or.inl ⟨hm,reduced_linear_comparison h p E₁ Q e split hm hc⟩
  · exact Or.inr ⟨hm,C2Source.reduced_comparison h p Q e split hm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
