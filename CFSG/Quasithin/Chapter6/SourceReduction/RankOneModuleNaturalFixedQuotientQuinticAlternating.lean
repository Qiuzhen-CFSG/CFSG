module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveProduct
public import Theory.GroupTheory.CoreCentralNormalizerAction.AlternatingFiveObstruction
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Excluding the original alternating central carriers

The original quintic residual is solvable and two-perfect. In an alternating
carrier its action is therefore inner, while its original faithful five-subgroup
ensures five divides the whole image order. The actual component Sylow maps
to a full Sylow normalizing this image. The small alternating Sylow-overgroup
order obstruction gives a contradiction, without a prime-square actor premise.

Source: Aschbacher--Smith A.3.15 and6.1.4, pp.50--51 and665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- No alternating group of degree at most eight is the literal simple
central carrier of the original outside component. -/
theorem original_hermitian_component_not_alternating
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (m : ℕ) (hm8 : m ≤ 8) :
    ¬ Nonempty (coreCentralQuotient K ≃* alternatingGroup (Fin m)) := by
  rintro ⟨e⟩
  let := hq
  let C := coreCentralQuotient K
  let : IsSimpleGroup C := IsQuasisimple.simple
  let : IsQuasisimple C := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center (K ⧸ pCore 2 K))) (QuotientGroup.mk'_surjective _)
  have hm5 : 5 ≤ m := by
    by_contra hn
    let emb : Fin m ↪ Fin 4 := Fin.castLEEmb (by omega)
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin m)) :=
      Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective emb)
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
      (f := (alternatingGroup (Fin m)).subtype.comp e.toMonoidHom)
      ((alternatingGroup (Fin m)).subtype_injective.comp e.injective)
    exact Group.IsPerfect.not_isSolvable C inferInstance
  let X := quinticResidual T L
  have hi := h.rankOneInput hout
  let : Group.IsSolvable (localBorel T L) :=
    localBorel_isSolvable hi.exponent hi.linear hi.sylow_normalizes
  have hXB : X ≤ localBorel T L := map_subtype_le _
  have hsolv : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hXB)
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) M₁ :=
    ⟨T.subtype hTM₁,map_subgroupOf_eq_of_le hTM₁⟩
  obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G) := by
    rw [hU]
    exact inf_le_left.trans (sylow_normalizes_quinticResidual hi.sylow_normalizes)
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDimage := original_hermitian_quintic_central_image_card
    h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have h5 : 5 ∣ Nat.card (coreCentralActorImage K X) := hDimage ▸
    card_dvd_of_le (map_mono (subgroupOf_mono (normalizer (K : Set G)) hDX))
  exact coreCentral_no_small_alternating_quintic K X U hUX hXN
    (quinticResidual_twoPerfect T L) hsolv h5 m (by omega) e

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
