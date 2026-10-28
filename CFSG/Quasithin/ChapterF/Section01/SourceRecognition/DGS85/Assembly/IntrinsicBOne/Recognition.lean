module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.Profile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.BinaryAmalgam
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneTriangular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneQuadrangular

/-!
# Intrinsic noncommuting b=1 marked source recognition

The earlier intrinsic Chapter 7–10 theorem constructs both natural actions
and synchronizes the two source path alternatives. At field order two the
faithful small-amalgam argument identifies the whole reduced inclusion pair.
For larger fields the actions construct full Cartan profiles; the established
triangular and quadrangular arguments supply their actual finite marked split
quotients. The existing quotient recognizer then gives the native flag models.

The final theorem has only the unchanged original F.1.11, critical-pair,
noncommuting and b=1 hypotheses. It produces a small finite field of positive
binary degree, orientation, and an isomorphism of the literal reduced amalgam,
including the whole Borel and both inclusion squares. Its reduced-alternatives
consumer retains that marking. Original extension restoration and other
critical branches remain with final source assembly.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126–127; (10.5),
pp.156–157; Chapter 14 and Theorem D, pp.210–224. AS F.1.12, pp.262–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
open Reduction OriginalExtension NoncommutingProfile SuzukiContainment
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local instance {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

private theorem full_profiles_of_nonbinary
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (h : HypothesisF11 L S)
    (p : C2Source.Profile L S k₀ k₁ (Fin 2 → k₀) (Fin 2 → k₁))
    (hk : 2 < Nat.card k₀) (c : CompatibleCartans L (reducedSylow L S)) :
    Nonempty (∀ j : Bool, FullCartanReflectionProfile.{u} h c j) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) p.left p.right
  have hk₁ : 2 < Nat.card k₁ :=
    (paired_field_orders_eq (reduced_triple h) p.left p.right p.natural) ▸ hk
  obtain ⟨d₀⟩ := BOneSource.full_cartan_profile_of_action h false p.left c p.left_actor hc₁ p.natural hk
  obtain ⟨d₁⟩ := BOneSource.full_cartan_profile_of_action h true p.right c p.right_actor hc₀
    (LinearEquiv.refl (ZMod 2) _) hk₁
  exact ⟨fun j => by cases j; exact d₀; exact d₁⟩

/-- Full marked reduced recognition from the unchanged original noncommuting
b=1 source hypotheses, including the binary fields and the whole Borel.
This statement does not identify the ambient completion with a finite group. -/
theorem small_comparison_of_critical_bOne
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam F point))) ∨
       (∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam F point)))) := by
  obtain ⟨k₀,f₀,fin₀,ch₀,k₁,f₁,fin₁,ch₁,_,⟨p⟩⟩ := profile_of_critical_bOne h hc hne hb
  by_cases hk : Nat.card k₀=2
  · refine ⟨ZMod 2,inferInstance,inferInstance,inferInstance,1,by decide,by simp,?_⟩
    rcases binary_reduced_comparison h p hk with hl | hs
    · exact Or.inl ⟨false,hl⟩
    · exact Or.inr ⟨true,hs⟩
  · have hkgt : 2 < Nat.card k₀ := by have := Finite.one_lt_card (α := k₀); omega
    let c := chosenCartans h
    obtain ⟨ds⟩ := full_profiles_of_nonbinary h p hkgt c
    obtain ⟨r,hr,_,_,hparams,_,_⟩ :=
      NoncommutingProfile.Reduction.original_bOne_intrinsic_tree_profile h hc hne hb
    rcases hr with rfl | rfl
    · obtain ⟨F,f,fin,ch,m,hm,hF,he⟩ := small_comparison_of_marked_quotient h hc hne hb
        (fullCartanRThreeFiniteQuotient ds hparams) (fullCartanRThreeFiniteMarkedIso ds hparams)
        (fullCartanRThreeFiniteSplitData ds hparams)
      exact ⟨F,f,fin,ch,m,hm,hF,he.imp And.right And.right⟩
    · obtain ⟨F,f,fin,ch,m,hm,hF,he⟩ := small_comparison_of_marked_quotient h hc hne hb
        (BOneSource.fullCartanRFourFiniteQuotient ds hparams)
        (BOneSource.fullCartanRFourFiniteMarkedIso ds hparams)
        (BOneSource.fullCartanRFourFiniteSplitData ds hparams)
      exact ⟨F,f,fin,ch,m,hm,hF,he.imp And.right And.right⟩

/-- The literal reduced-alternatives consumer, without a marked-quotient,
actor-model or nonsolvability premise. Original extension restoration remains
with the source assembly owner. -/
theorem reduced_alternatives_of_critical_bOne {A B : Subgroup G}
    (h : HypothesisF11 ![A,B] S) {v w : Vertex (reducedFamily ![A,B] S)}
    (hc : IsCriticalPair (reducedFamily ![A,B] S) v w)
    (hne : ⁅Z (reducedFamily ![A,B] S) v,Z (reducedFamily ![A,B] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![A,B] S) = 1) :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives A B S := by
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ := small_comparison_of_critical_bOne h hc hne hb
  rcases he with ⟨point,hf⟩ | ⟨point,hf⟩
  · exact .linear F m hm hF point hf
  · exact .symplectic F m hm hF point hf

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.IntrinsicBOne
