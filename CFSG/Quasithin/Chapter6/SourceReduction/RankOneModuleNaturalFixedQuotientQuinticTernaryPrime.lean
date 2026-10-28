module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryInner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SU3.TernaryPerfectCover

/-!
# The original odd ternary parameter is greater than three

The whole original action is inner, and its faithful five-subgroup forces
five to divide the actual central carrier order. Both ternary models at
the prime three have five-free order. This supplies the strict parameter
bound needed for the genuine SL₂ component of an involution centralizer.

Source: Aschbacher--Smith6.1.4, odd ternary case, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The actual odd ternary central carrier has a factor five, and its
original field prime exceeds three. -/
theorem original_hermitian_quintic_odd_three_card_and_prime
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign (coreCentralQuotient K) unitary 3 p) :
    5 ∣ Nat.card (coreCentralQuotient K) ∧ 3 < p := by
  let C := coreCentralQuotient K
  have hinner : coreCentralActorImage K (quinticResidual T L) ≤ MulAut.innerSubgroup C := by
    cases unitary with
    | false => exact original_hermitian_quintic_odd_linear_three_inner h hout hm hM₁ hCM₁ hK hq p hp ho hc
    | true => exact original_hermitian_quintic_odd_unitary_three_inner h hout hm hM₁ hCM₁ hK hq p hp ho hc
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDimage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have h5I : 5 ∣ Nat.card (MulAut.innerSubgroup C) := hDimage ▸
    card_dvd_of_le ((map_mono (subgroupOf_mono _ hDX)).trans hinner)
  have h5 : 5 ∣ Nat.card C := h5I.trans
    (card_dvd_of_surjective (MulAut.conj : C →* MulAut C).rangeRestrict
      (MulAut.conj : C →* MulAut C).rangeRestrict_surjective)
  refine ⟨h5,?_⟩
  by_contra hn
  have hp2 := hp.two_le
  have hpne : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
  have he : p = 3 := by omega
  subst p
  cases unitary with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at hcard
    norm_num [Fin.prod_univ_succ] at hcard
    have horder : Nat.card PSL(3,F) = 5616 := by omega
    rw [Nat.card_congr e.toEquiv,horder] at h5
    norm_num at h5
  | true =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hc
    rw [Nat.card_congr e.toEquiv,
      BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hconj] at h5
    norm_num at h5

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
