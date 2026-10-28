module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import Theory.Mathieu.QuinticSylowActors

/-!
# Excluding the original larger Mathieu central carriers

The literal component action supplies a normal copy of its simple central
quotient, the faithful original five-image and an actual full Sylow. Their
permuting product has order a power of two times five. The native Mathieu
Sylow-overgroup obstructions exclude M₂₂, M₂₃ and M₂₄ on these same objects.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original outside component has none of the three larger Mathieu
groups as its literal simple central quotient. -/
theorem original_hermitian_component_not_larger_mathieu
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ (Nonempty (coreCentralQuotient K ≃* Sporadic.Mathieu.M22) ∨
       Nonempty (coreCentralQuotient K ≃* Sporadic.Mathieu.M23) ∨
       Nonempty (coreCentralQuotient K ≃* Sporadic.Mathieu.M24)) := by
  intro he
  let A := coreCentralActorImage K M₁
  let N := (MulAut.innerSubgroup (coreCentralQuotient K)).subgroupOf A
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hC,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let : N.Normal := hN
  apply Sporadic.Mathieu.QuinticSylowActors.no_five_actor N E S (a := a) _ hE
    (by rw [hC]; exact disjoint_bot_right) hcard
  rcases he with he | he | he
  · exact Or.inl ⟨eN.trans he.some⟩
  · exact Or.inr (Or.inl ⟨eN.trans he.some⟩)
  · exact Or.inr (Or.inr ⟨eN.trans he.some⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
