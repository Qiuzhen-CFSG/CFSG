module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerPushingUp

/-!
# Completion of the degree-five odd-normalizer argument

Nonsingular-centralizer control excludes the full doubled orbit in the
central two-cover produced by pushing up. The orbit embeds in its central
quotient by its fixed-space calculation; the covering center is retained.
Thus the actual odd fixed residual has unique maximal overgroup. The checked
unique-residual argument then controls every abelian odd actor, and the
characteristic abelian reduction handles every original odd-order subgroup.

Source: Aschbacher--Smith 4.2.13, 4.4.3--12 and 12.1.9, pp.612,619--623,793.
ReductionSource.DoubleNaturalExcludedOddNormalizers applies this to the
original degree-five doubled branch and the E.3.35 terminal contradiction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  {n : ℕ} (B : DoubledBranch T L V n)
include D h B

/-- Nonsingular control excludes an injectively placed orbit in a central two-cover. -/
theorem doubledOrbit_no_janko_two_cover_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (K : Subgroup G) (hW : componentOrbit V (T : Subgroup G) ≤ K)
    (hZ : IsPGroup 2 (center K))
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hi : Function.Injective ((QuotientGroup.mk' (center K)).comp (inclusion hW))) : False := by
  let := D.doubledOrbit_elementary h
  let W := componentOrbit V (T : Subgroup G)
  have hn : 0 < n := by have := B.degree; omega
  let i : Fin n := ⟨0,hn⟩
  let v : BinaryLinear.OuterCyclic.Space n := fun _ => 1
  let φ : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj i
  let w : W := B.coordinates.symm (Multiplicative.ofAdd (v,φ))
  have hq : B.quadratic (Additive.ofMul w) ≠ 0 := by
    rw [B.quadratic_apply]
    change (B.coordinates (B.coordinates.symm (Multiplicative.ofAdd (v,φ)))).toAdd.2
      (B.coordinates (B.coordinates.symm (Multiplicative.ofAdd (v,φ)))).toAdd.1 ≠ 0
    rw [B.coordinates.apply_symm_apply]
    exact one_ne_zero
  have hw : w ≠ 1 := by
    intro he
    apply hq
    rw [he]
    exact B.quadratic.map_zero
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian (w : G) w.property,
      fun he => hw (Subtype.ext he)⟩
  let U := W.subgroupOf K
  let a : U ≃* W := subgroupOfEquivOfLe hW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  have hcard : Nat.card U = 256 ∨ Nat.card U = 1024 := by
    rw [Nat.card_congr a.toEquiv]
    have hc : Nat.card W = 2 ^ (2 * n) := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rw [Nat.card_congr Additive.toMul,B.finrank_eq,Nat.card_zmod] at hh
      exact hh
    rw [hc]
    rcases B.degree with rfl | rfl <;> norm_num
  let z : K := ⟨w,hW w.property⟩
  have hz2 : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans hw2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hif : Function.Injective (f.comp U.subtype) := by
    intro x y he
    apply a.injective
    apply hi
    exact e.injective he
  apply Janko4.InvolutionCentralizers.no_large_elementary_controlled_involution_central_two_cover
    f hf hk.le (hk ▸ hZ) U hif hcard z w.property hz2
  intro x hx
  have hxC : (x : G) ∈ centralizer ({(w : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg K.subtype (mem_centralizer_singleton_iff.mp hx)
  have hxM := (D.doubleNatural_nonsingular_controls_of_many h hmany B).1 w hq hxC
  rw [←D.doubledOrbit_normalizer_eq h B.orbit_eq] at hxM
  intro y
  exact hxM (y : G)

omit B in
/-- Failure of uniqueness would produce the excluded central J₄ cover. -/
theorem doubledFive_oddActorResidual_unique_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,U,hw,hWU,hWJ,K,hK,hn,hout,hUK,hWK,⟨e⟩⟩ :=
    D.doubledFive_pushingUp_janko h B A hA ho hnot
  let Kg := K.map H.subtype
  let q : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : IsQuasisimple K := hK.2
  have hc := hw.2.2.2.2.2.2.1
  have hZK : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hZ : IsPGroup 2 (center Kg) := hZK.of_equiv (centerCongr q.symm)
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  exact D.doubledOrbit_no_janko_two_cover_of_many h B hmany Kg hWK hZ
    ((Chapter4.Section02.RankOneReciprocalEscape.centerQuotientCongr q).trans e)
    (D.doubledOrbit_cover_quotient_injective h B hWK hFK hw.2.2.2.2.2.2.2.1)

omit B in
/-- Source 12.1.9(1), for every original nontrivial odd subgroup in degree five. -/
theorem doubledFive_oddNormalizer_control_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  exact hout (D.doubledFive_oddNormalizer_control_of_unique_of_many h hmany B _ hne hA ho
    (D.doubledFive_oddActorResidual_unique_of_many h hmany B _ hA ho))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
