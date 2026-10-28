module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerInner
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoExclusion
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.NormalElementary

/-!
# Excluding the actual J₄ odd-normalizer component

Choose a nonsingular vector in the original doubled orbit. The proved
12.1.1 control makes its ambient centralizer normalize that orbit. An
embedding of the orbit into any odd central cover of J₄ contradicts the
native involution-centralizer obstruction, with both the original point
and the literal quotient map retained.

In degree five, residual uniqueness and the complete outer/model exclusions
place the full orbit in a normal J₄ component. Its odd centralizer supplies
oddness of the covering center, so this branch gives the original odd-actor
normalizer containment. The separate pushing-up branch still requires proof;
no residual-uniqueness premise is asserted unconditionally here.

Source: Aschbacher--Smith, 4.4.10--12 and 12.1.1/9, pp.621--623,788,793.
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

/-- Nonsingular control excludes the full original orbit from an actual
odd central cover of J₄, in both degrees. -/
theorem doubledOrbit_no_janko_odd_cover_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {K : Type*} [Group K] [Finite K]
    (j : K →* G) (hj : Function.Injective j)
    (hW : componentOrbit V (T : Subgroup G) ≤ j.range)
    (hodd : Odd (Nat.card (center K)))
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
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
  let U := W.comap j
  have hmap : U.map j = W := map_comap_eq_self hW
  let a : U ≃* W := (U.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hmap)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  have hcard : Nat.card U = 256 ∨ Nat.card U = 1024 := by
    rw [Nat.card_congr a.toEquiv]
    have hc : Nat.card W = 2 ^ (2 * n) := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rw [Nat.card_congr Additive.toMul,B.finrank_eq,Nat.card_zmod] at hh
      exact hh
    rw [hc]
    rcases B.degree with rfl | rfl <;> norm_num
  obtain ⟨z,hz⟩ := hW w.property
  have hzU : z ∈ U := by
    change j z ∈ W
    rw [hz]
    exact w.property
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective j hj z,hz]
    exact hw2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact hodd.coprime_two_left
  apply Janko4.InvolutionCentralizers.no_large_elementary_controlled_involution_cover
    f hf hk U hcard z hzU hz2
  intro x hx
  have hxC : j x ∈ centralizer ({(w : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hz]
    simpa only [map_mul] using congrArg j (mem_centralizer_singleton_iff.mp hx)
  have hxM := (D.doubleNatural_nonsingular_controls_of_many h hmany B).1 w hq hxC
  rw [← D.doubledOrbit_normalizer_eq h B.orbit_eq] at hxM
  intro y
  change j y ∈ W ↔ j (x * y * x⁻¹) ∈ W
  simpa only [SetLike.mem_coe,W,map_mul,map_inv] using hxM (j y)

omit B in
/-- The unique-residual branch of the original degree-five odd normalizer
argument is impossible outside the original normalizer. -/
theorem doubledFive_oddNormalizer_control_of_unique_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨K,hK,hn,hw,hf,hc,hr,⟨e⟩⟩ :=
    D.doubledFive_oddNormalizer_janko_of_unique h B A hne hA ho hu hout
  let N := normalizer (A : Set G)
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  apply D.doubledOrbit_no_janko_odd_cover_of_many h B hmany (N.subtype.comp K.subtype)
    (N.subtype_injective.comp K.subtype_injective) _ hoZ e
  simpa only [MonoidHom.range_comp,range_subtype] using hw

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
