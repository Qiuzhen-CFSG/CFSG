module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryPrime
public import Theory.SpecificGroups.PSL3.QuinticInvolutionBlock
public import Theory.SpecificGroups.SU3.QuinticInvolutionBlock

/-!
# The actual rank-one block in the original ternary carrier

The involution centralizer is taken in the original core-central quotient.
Its literal commutator is SL₂ over the original field prime. The centralizer
of this block inside the involution centralizer is precisely its center.
Both statements transport along the source model identification.

Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels

private theorem centralizer_commutator_eq_center_of_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : centralizer (commutator B : Set B) = center B) :
    centralizer (commutator A : Set A) = center A := by
  apply le_antisymm
  · intro a ha
    have he : e a ∈ centralizer (commutator B : Set B) := by
      intro b hb
      have hm : (commutator A).map e.toMonoidHom = commutator B := by
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
        rfl
      obtain ⟨x,hx,rfl⟩ := hm.symm ▸ hb
      exact (e.map_mul _ _).symm.trans ((congrArg e (ha x hx)).trans (e.map_mul _ _))
    rw [hB] at he
    apply mem_center_iff.mpr
    intro x
    exact e.injective (by simpa only [map_mul] using mem_center_iff.mp he (e x))
  · exact center_le_centralizer _

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original ternary involution centralizer has the literal characteristic
SL₂ block, and its centralizing branch lies in the center. -/
theorem original_hermitian_quintic_ternary_involution_block
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign (coreCentralQuotient K) unitary 3 p)
    (z : coreCentralQuotient K) (hz : orderOf z = 2) :
    let C := centralizer ({z} : Set (coreCentralQuotient K))
    Nonempty (commutator C ≃* SL(2,ZMod p)) ∧
      centralizer (commutator C : Set C) = center C := by
  let : Fact p.Prime := ⟨hp⟩
  have hlarge := (original_hermitian_quintic_odd_three_card_and_prime
    h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc).2
  cases unitary with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    have h2 := GorensteinWalter.two_ne_zero_of_odd_card F (hF.symm ▸ ho)
    obtain ⟨⟨b⟩,hcent⟩ := Matrix.PSL3.TwoFiveSylow.involution_centralizer_commutator_structure
      (by rw [hF]; exact hlarge) h2 (e z) ((e.orderOf_eq z).trans hz)
    let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e z
    let _ := Fintype.ofFinite F
    let ef : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq
      (by simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact ⟨⟨((Matrix.SU3.InnerThreeRank.commutatorEquiv c).trans b).trans
      (GorensteinWalter.sl2RingEquiv ef)⟩,
      centralizer_commutator_eq_center_of_equiv c hcent⟩
  | true =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hc
    obtain ⟨⟨b⟩,hcent⟩ := Matrix.SU3.TwoFiveSylow.involution_centralizer_commutator_structure
      p ho hlarge F J hF hconj (e z) ((e.orderOf_eq z).trans hz)
    let c := Matrix.SU3.InnerThreeRank.centralizerEquiv e z
    exact ⟨⟨(Matrix.SU3.InnerThreeRank.commutatorEquiv c).trans b⟩,
      centralizer_commutator_eq_center_of_equiv c hcent⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
