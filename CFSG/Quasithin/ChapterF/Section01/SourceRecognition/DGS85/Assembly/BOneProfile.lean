module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneBorelSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability
/-!
# Constructing the b=1 recognition profile from a critical pair

The Chapter 7 natural-section theorem constructs both actions on the literal
reduced graph. Its source actor identities give the two fields of the marked
C₂ profile, while the constructed spaces are already the two-dimensional
natural spaces. Thus both natural-space equivalences are identities.
For nonsolvable original parabolics, the proved small-unitary exclusions
supply all enlarged actor models as well. Applying the order comparison and
marked recognition then produces A₂ or C₂ with the whole Borel and both
endpoint squares, including the binary fields.

The distance-one noncommuting critical branch and the actual marked split
quotient remain earlier inputs. This does not assert exhaustiveness.
Source: DGS, Groups and Graphs (1985), (7.1), pp.126--127,
(10.4)--(10.5), pp.155--157, and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
open Reduction NoncommutingProfile Noncommuting.Reduction
open Subgroup.CosetGeometry.RankTwo
open OriginalExtension FongSeitzBinary
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- Construct both original source actors and natural spaces from the critical pair. -/
theorem profile_of_actor_models
    (h : HypothesisF11 L S)
    (hm : ∀ x : Vertex (reducedFamily L S), IsRankOneModel
      (graphLocalGroup (reducedFamily L S) x ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) x)))
    {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2),
      let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      Nonempty (C2Source.Profile L S k₀ k₁ (Fin 2 → k₀) (Fin 2 → k₁)) := by
  obtain ⟨_, _, k₀, f₀, n₀, ch₀, a₀, k₁, f₁, n₁, ch₁, a₁,
      c₀, c₁, ha₀, ha₁, _, _, _⟩ :=
    original_bOne_natural_cores_of_actor_models h hm hc hne hb
  have haeq₀ : a₀ = ZMod.algebra k₀ 2 := Subsingleton.elim _ _
  have haeq₁ : a₁ = ZMod.algebra k₁ 2 := Subsingleton.elim _ _
  subst a₀ a₁
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  exact ⟨k₀, f₀, n₀, ch₀, k₁, f₁, n₁, ch₁,
    ⟨⟨c₀, c₁, ha₀.trans (reduced_base_actor_eq_source h false),
      ha₁.trans (reduced_base_actor_eq_source h true), LinearEquiv.refl (ZMod 2) _⟩⟩⟩

/-- Nonsolvability of the actual parabolics discharges the setup actor-model premise. -/
theorem profile_of_nonsolvable_parabolics
    (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2),
      letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      Nonempty (C2Source.Profile L S k₀ k₁ (Fin 2 → k₀) (Fin 2 → k₁)) :=
  profile_of_actor_models h (reduced_actor_models_of_nonsolvable_parabolics h hns) hc hne hb

/-- Actual source recognition with both actions, actor equalities and natural
space markings constructed from the distance-one noncommuting critical pair. -/
theorem comparison_of_critical_bOne
    (h : HypothesisF11 L S)
    (hm : ∀ x : Vertex (reducedFamily L S), IsRankOneModel
      (graphLocalGroup (reducedFamily L S) x ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) x)))
    {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2),
      (rotationOrder Q = 3 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam k₁ point))) ∨
      (rotationOrder Q = 4 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam k₀ point))) := by
  obtain ⟨k₀,f₀,n₀,ch₀,k₁,f₁,n₁,ch₁,⟨p⟩⟩ :=
    profile_of_actor_models h hm hc hne hb
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  exact ⟨k₀,f₀,n₀,ch₀,k₁,f₁,n₁,ch₁,
    reduced_comparison h p (LinearEquiv.refl (ZMod 2) _) Q e split⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
