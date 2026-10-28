module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.PrimeActors

/-!
# Excluding the original Rudvalis central carrier

The actual simple central quotient supplies the trivial ambient two-core.
The proved native two-core and radical-normalizer coverage then constructs
the full Rudvalis Sylow-overgroup cover. Its quintic order obstruction applies
to the original faithful five-image and actual effective Sylow product.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original outside component cannot have Rudvalis as its literal
central quotient; no Sylow-overgroup coverage is assumed. -/
theorem original_hermitian_component_not_rudvalis
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let := hq
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient K) := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcore : pCore 2 Rudvalis.Model = ⊥ := by
    rcases (inferInstance : (pCore 2 Rudvalis.Model).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 Rudvalis.Model := by
        have hh := pCore_isPGroup (p := 2) (G := Rudvalis.Model)
        rw [ht] at hh
        exact hh.of_equiv topEquiv
      let := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable Rudvalis.Model inferInstance).elim
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover
    hcore Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hcent,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let := hN
  exact Rudvalis.SylowOvergroups.no_five_actor hcover _ E S (eN.trans e) hE
    (by rw [hcent]; exact disjoint_bot_right) hcard

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
