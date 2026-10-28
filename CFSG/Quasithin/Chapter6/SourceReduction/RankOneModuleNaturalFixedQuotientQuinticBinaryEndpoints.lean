module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEvenExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticAlternating
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.SpecificGroups.Triality.BinaryPrimeActors

/-!
# The original rank-two component reduces to Tits

The faithful original five-image forces five to divide the full automorphism
group of the literal central quotient. The field-two linear, G₂-derived and
triality carriers have five-free automorphism groups. The symplectic-derived
carrier is the actual alternating group on six letters, already excluded by
the original Sylow argument. Only the explicit Tits alternative remains.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels
open Chapter1.XiEmbedding.InvariantLarge
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original quintic image excludes four of the five binary endpoints;
the Tits model remains a genuine alternative. -/
theorem original_hermitian_rankTwo_component_tits
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : RankTwoTheoremC (coreCentralQuotient K)) :
    Nonempty (coreCentralQuotient K ≃* Tits.ParrottGroup) := by
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDimage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have h5 : 5 ∣ Nat.card (MulAut (coreCentralQuotient K)) :=
    hDimage ▸ (coreCentralActorImage K D).card_subgroup_dvd_card
  have he := original_hermitian_rankTwo_component_small h hout hm hM₁ hCM₁ hK hnot hq hc
  rcases he with he | he | he | he | he
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let eC := e.trans (Atlas.fieldEquivPSL 3 eF)
    rw [Nat.card_congr (MulAut.congr eC).toEquiv,
      Matrix.PSL3Two.Automorphisms.card_aut] at h5
    norm_num at h5
  · obtain ⟨P,hP,⟨e⟩⟩ := he
    have hp := P.eq_binaryParameters_of_q_eq 1 Nat.zero_lt_one (by simpa using hP)
    subst P
    exact (Triality.Standard.BinaryPrimeActors.five_not_dvd_card_aut
      ((Nat.card_congr (MulAut.congr e).toEquiv) ▸ h5)).elim
  · obtain ⟨e⟩ := he
    exact (original_hermitian_component_not_alternating h hout hm hM₁ hCM₁ hK hnot hq
      6 (by decide) ⟨e.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩).elim
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      ← Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv,
      Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at h5
    norm_num at h5
  · exact he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
