module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddInverter
public import Theory.GroupTheory.PResidual.InverterPlacement

/-!
# The original quintic residual lies in the odd linear-two component

An inverter from the original T∩K acts modulo the whole O₂(X). Since X
normalizes K and is two-perfect, this forces X≤K in the original group.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original two-perfect quintic residual is contained in the original
component, before taking either its two-core or central quotient. -/
theorem original_hermitian_quintic_le_odd_linear_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    quinticResidual T L ≤ K := by
  obtain ⟨k,_,_,hkinv⟩ := original_hermitian_quintic_odd_linear_sylow_inverter
    h hout hm hM₁ hCM₁ hK hnot hq p d hp ho hd hc
  exact le_of_normalized_inverter (quinticResidual T L) K
    (quinticResidual_twoPerfect T L)
    (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)
    k k.property hkinv

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
