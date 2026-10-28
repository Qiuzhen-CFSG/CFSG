module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalAutomizer
public import Theory.Representation.AbelianWeightAutomizerBounds

/-!
# Excluding component quotients with small faithful representations

The local module meets the covering center trivially when the component has
zero two-core. A faithful representation of the central quotient is therefore
faithful on that module, even when its pullback is not faithful on the cover.
The weight-permutation bound contradicts the doubled odd ranks supplied by
the actual residual action. A nontrivial perfect component has an odd prime
divisor different from three, so a degree bound of eight suffices.

Source: Aschbacher--Smith 4.4.3 and 10.2.3(2), printed pp.622 and 745.
-/

public section
open scoped Pointwise
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
private theorem elementary_center_quotient_injective
    {K : Type*} [Group K] [Finite K] (W : Subgroup K)
    [IsElementaryAbelian 2 W] (hc : pCore 2 K = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp W.subtype) := by
  let C := W ⊓ center K
  have hC : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have he := mem_center_iff.mp hx.2 g
    rw [he,mul_inv_cancel_right]
    exact hx
  have hle : C ≤ pCore 2 K :=
    le_sSup ⟨hC,(IsElementaryAbelian.isPGroup 2 W).to_le inf_le_left⟩
  have hb : C = ⊥ := bot_unique (hle.trans_eq hc)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro w hw
  exact Subtype.ext (show (w : K) = 1 from hb.le
    ⟨w.property,(QuotientGroup.eq_one_iff _).mp hw⟩)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A faithful small-degree representation of the central quotient excludes a placed component. -/
theorem source_nonnormal_oddNormalizer_no_placed_small_degree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G) (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] (h2 : (2 : F) ≠ 0)
    (σ : Representation F (K ⧸ center K) U) (hσ : Function.Injective σ)
    (hdim : Module.finrank F U ≤ 8) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  obtain ⟨r,hr,hpo,h3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card S Nat.prime_three
  let : Fact r.Prime := ⟨hr⟩
  let W := (V.subgroupOf (normalizer (B : Set G))).subgroupOf K
  obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  let : IsElementaryAbelian 2 W := hW
  let q := QuotientGroup.mk' (center K)
  let ρ := σ.comp q
  have hf : Function.Injective (ρ.comp W.subtype) :=
    hσ.comp (elementary_center_quotient_injective W hc)
  have horder : (Nat.card W : F) ≠ 0 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_ne_zero _ h2
  have hup := Representation.automizer_odd_rank_le_one_of_degree_eight ρ W hf horder
    hdim hpo h3
  have hlo := source_nonnormal_oddNormalizer_fullModule_automizer_rank D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hFK hpo
  have hpos : 0 < primeRank r S := Nat.pos_of_ne_zero
    (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd)
  change 2 * primeRank r S ≤ primeRank r W.normalizerMonoidHom.range at hlo
  omega

end CFSG.Quasithin.Chapter10.LocalFixed
