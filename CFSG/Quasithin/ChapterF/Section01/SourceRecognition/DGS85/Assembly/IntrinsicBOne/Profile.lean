module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneIntrinsicSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCriticalConsumers

/-!
# The intrinsic b=1 profile at the marked recognition boundary

The natural actions and their actual actor identities come from the original
noncommuting critical pair. Thus the marked-quotient consumer needs no separate
catalogue of all vertex actors. Both fields and the entire reduced amalgam are
retained. Construction of the marked quotient is a separate obligation.

Source: DGS, *Groups and Graphs* (1985), (7.1) and (10.5), pp.126–127,156–157.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
open Reduction OriginalExtension NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local instance {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k :=
  ZMod.algebra k 2

/-- The earlier intrinsic theorem constructs both natural profiles, with the
same equal field orders and the literal source actors. -/
theorem profile_of_critical_bOne
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2),
      letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
      letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      Nat.card k₀ = Nat.card k₁ ∧
        Nonempty (C2Source.Profile L S k₀ k₁ (Fin 2 → k₀) (Fin 2 → k₁)) := by
  obtain ⟨_,_,_,_,_,k₀,f₀,fin₀,ch₀,k₁,f₁,fin₁,ch₁,c₀,c₁,ha₀,ha₁,hfields,_⟩ :=
    NoncommutingProfile.Reduction.original_bOne_complete_profile h hc hne hb
  exact ⟨k₀,f₀,fin₀,ch₀,k₁,f₁,fin₁,ch₁,hfields,
    ⟨⟨c₀,c₁,ha₀.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h false),
      ha₁.trans (Noncommuting.Reduction.reduced_base_actor_eq_source h true),
      LinearEquiv.refl (ZMod 2) _⟩⟩⟩

/-- Literal application to the existing small-field recognition consumer.
Only the actual marked split quotient remains explicit. -/
theorem small_comparison_of_marked_quotient
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((rotationOrder Q = 3 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam F point))) ∨
      (rotationOrder Q = 4 ∧ ∃ point : Bool,
        Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam F point)))) := by
  apply BOneSource.small_comparison_of_critical_bOne h ?_ hc hne hb Q e split
  intro x
  have he : (graph (reducedFamily L S)).Adj v w :=
    SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  obtain ⟨n,hn,hm⟩ := reduced_cross_orbit_actor_models h hc hne he.1 x
  exact .linear n hn hm

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
