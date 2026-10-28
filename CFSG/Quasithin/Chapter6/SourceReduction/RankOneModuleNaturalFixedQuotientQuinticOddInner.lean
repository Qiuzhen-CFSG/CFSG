module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveProduct
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup

/-!
# Inner placement of the original quintic actor in odd linear-two rows

The full outer automorphism group of PSL₂(p) and PSL₂(p²) is a two-group.
The original quintic residual is two-perfect, so its literal action on the
central quotient has trivial outer image. This places the entire actor
image in the actual inner subgroup, without assuming its placement or
identifying the original component with its central quotient.

Source: Aschbacher--Smith A.3.15(1), printed p.50, used in 6.1.4, p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- In either actual odd linear-two row, the whole original quintic action
is inner on the literal central carrier. -/
theorem original_hermitian_quintic_odd_linear_inner
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁)
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d ≤ 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    coreCentralActorImage K (quinticResidual T L) ≤
      MulAut.innerSubgroup (coreCentralQuotient K) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
  have houter : IsPGroup 2 (MulAut.Outer (coreCentralQuotient K)) :=
    (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho hd hF).of_equiv
      (MulAut.outerCongr e).symm
  let X := quinticResidual T L
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let f : X →* MulAut (coreCentralQuotient K) :=
    (normalizerCoreCentralAction K).comp (inclusion hXN)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (coreCentralQuotient K))
  have hz := (quinticResidual_twoPerfect T L).hom_eq_one_of_isPGroup houter (q.comp f)
  rintro _ ⟨a,ha,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hz ⟨a.val,ha⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
