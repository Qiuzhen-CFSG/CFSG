module
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Reduction
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Torus
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.GroupAction.ComponentRankAction.ResidualSource
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Odd-prime actors in binary symplectic components

A rank-two odd prime in Sp₄(q) divides q²−1. Otherwise the group order
and the faithful four-dimensional representation make its Sylow subgroup
cyclic. Two orthogonal SL₂ planes then supply elementary order p².
The fixed-point congruence for a field actor of order p retains q²−1
modulo p, so the same elementary group occurs in its actual fixed group.
Adjoining that outer actor forces rank three. Consequently all p-elements
of an ambient group of p-rank at most two belong to the original component.

The result keeps the full covering center, assuming only its coprimality
to p. The literal nonblock application is in
NonblockEndgameSieveModelsNoncubicLie, for original 4.3.12(2).
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12, p.617.
-/

public section
open Subgroup
open scoped MatrixGroups
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.NondefiningPrimeActors
open DiagramAutomorphisms Theory.GroupAction.ComponentRankAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {p : ℕ} [Fact p.Prime]

omit [CharP F 2] in
private theorem cast_pow_eq_one_iff {k : ℕ} :
    (Nat.card F : ZMod p)^k = 1 ↔ p ∣ Nat.card F^k - 1 := by
  have hq : 1 ≤ Nat.card F^k := Nat.one_le_pow _ _ Nat.card_pos
  rw [← sub_eq_zero, ← Nat.cast_pow, ← Nat.cast_one,
    ← Nat.cast_sub hq, ZMod.natCast_eq_zero_iff]

/-- A nondefining rank-two prime in Sp₄ divides the quadratic torus order. -/
theorem quadratic_dvd_of_rank_two (ho : Odd p) (hr : 2 ≤ primeRank p (Sp F)) :
    p ∣ Nat.card F^2 - 1 := by
  let : Fintype F := Fintype.ofFinite F
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hpq : ¬ p ∣ Nat.card F := by
    obtain ⟨f,_,hf⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card,hf]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hd))
  by_contra hquad
  have hd : p ∣ Nat.card (Sp F) := by
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  rw [card_sp] at hd
  have hfour : p ∣ Nat.card F^4 - 1 :=
    (hp.dvd_mul.mp hd).resolve_left
      (hp.not_dvd_mul (fun h => hpq (hp.dvd_of_dvd_pow h)) hquad)
  have hq0 : (Nat.card F : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using hpq
  have hpos : 0 < orderOf (Nat.card F : ZMod p) :=
    (isOfFinOrder_iff_isUnit.mpr (isUnit_iff_ne_zero.mpr hq0)).orderOf_pos
  have hd4 : orderOf (Nat.card F : ZMod p) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one ((cast_pow_eq_one_iff (F := F)).mpr hfour)
  have hn2 : ¬ orderOf (Nat.card F : ZMod p) ∣ 2 := by
    intro he
    exact hquad ((cast_pow_eq_one_iff (F := F)).mp (orderOf_dvd_iff_pow_eq_one.mp he))
  have hdegree : 4 ≤ orderOf (Nat.card F : ZMod p) := by
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd4
    interval_cases horder : orderOf (Nat.card F : ZMod p) <;> norm_num [horder] at *
  let P : Sylow p (Sp F) := default
  let ρ := (Representation.symplecticNatural (k := F) 2).comp (P : Subgroup (Sp F)).subtype
  have hρ : Function.Injective ρ := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have hh := congrArg (fun t => (t (Pi.single j 1)) i) he
    simpa [ρ, Representation.symplecticNatural, Matrix.mulVec_single] using hh
  have hc : IsCyclic P := Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree
    P.isPGroup' (CharP.cast_ne_zero_of_ne_of_prime F hp (Ne.symm hp2))
    (by simpa only [Nat.card_eq_fintype_card] using hpq) ρ hρ (by
      simpa only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_fin] using hdegree)
  have hb := P.primeRank_le_one_of_isCyclic hc
  omega

omit [CharP F 2] in
/-- Two orthogonal SL₂ planes supply independent prime-order subgroups. -/
theorem exists_elementary_quadratic (hd : p ∣ Nat.card F^2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := SL(2,F)) p (by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup]
    exact dvd_mul_of_dvd_right hd _)
  let P := zpowers a
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let f : P × P →* Sp F :=
    CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom.comp
      (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom_injective he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,inferInstance,?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod,Nat.card_zpowers,ha,pow_two]

omit [CharP F 2] in
private theorem fixed_quadratic_dvd (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F^2 - 1) :
    p ∣ Nat.card (FieldFixedResidual.fixedField σ)^2 - 1 := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hσ,pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield P F) [MOD p] at hc
  have hK : FixedPoints.subfield P F = FieldFixedResidual.fixedField σ := by
    ext x
    change (∀ g : P, g • x = x) ↔ _
    rw [FieldFixedResidual.mem_fixedField]
    constructor
    · intro hx
      exact hx ⟨σ,mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rw [hK] at hc
  have hh := Nat.ModEq.sub_right (a := 1)
    (Nat.one_le_pow _ _ Nat.card_pos) (Nat.one_le_pow _ _ Nat.card_pos) (hc.pow 2)
  exact Nat.modEq_zero_iff_dvd.mp (hh.symm.trans hd.modEq_zero_nat)

omit [CharP F 2] in
/-- Prime-order field actors fix an actual elementary subgroup of order p². -/
theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F^2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAutomorphism σ).fixedSubgroup := by
  obtain ⟨B,hB,hcard⟩ := exists_elementary_quadratic (fixed_quadratic_dvd σ hσ hd)
  let := hB
  let f : Sp (FieldFixedResidual.fixedField σ) →* Sp F :=
    (fieldAutomorphism σ).fixedSubgroup.subtype.comp (FieldFixedResidual.fixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAutomorphism σ).fixedSubgroup.subtype_injective.comp (FieldFixedResidual.fixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((FieldFixedResidual.fixedEquiv σ).symm b).property

/-- Adjoining an outer field actor to its fixed elementary p² forces rank three. -/
theorem field_actor_rank_three (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAutomorphism σ ∈ A)
    (hd : p ∣ Nat.card F^2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hd
  let := hE
  let f : Sp F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact InvolutionNormalForms.inner_injective (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAutomorphism σ,hσA⟩
  have hfield : Function.Injective (fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAutomorphismHom hfield σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) :=
      ⟨g,congrArg Subtype.val he⟩
    have hs := InvolutionNormalForms.field_eq_one_of_inner σ hi
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAutomorphism σ y * g⁻¹ = fieldAutomorphism σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every odd-prime-power actor is inner when that prime has model rank two. -/
theorem primePower_actor_inner (hF : 2 < Nat.card F) (ho : Odd p)
    (hr : 2 ≤ primeRank p (Sp F)) (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut (Sp F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup (Sp F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  have hd := quadratic_dvd_of_rank_two ho hr
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := OddFieldActors.inner_field_of_primePower hF ho a ham
  have hσA : fieldAutomorphism σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hp : IsPGroup p (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : p ∣ Nat.card (zpowers σ) := hp.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hn (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' p hdP
    have hτA : fieldAutomorphism (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAutomorphismHom (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three A hinner τ hτp hτA hd
    omega
  rw [he,hσone]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := fieldAutomorphismHom.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩

/-- The original component absorbs every ambient p-element, retaining its full center. -/
theorem component_eq_primeClosure_and_residual
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (hF : 2 < Nat.card F) (ho : Odd p) (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* Sp F) :
    L = closure {x : G | orderOf x = p} ∧ L = primeToResidual p G := by
  let := hL.2
  have hrmodel : 2 ≤ primeRank p (Sp F) := by
    rw [← primeRank_congr p e, ← primeRank_eq_of_surjective_of_coprime p
      (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective (center L))
      (by rwa [QuotientGroup.ker_mk'])]
    exact hr
  apply Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    hL hz hr hG e
  intro a ha m hm
  exact primePower_actor_inner hF ho hrmodel _ (inner_le_range L e)
    (range_rank_le_two L e hz hr hG) a ha ⟨m,hm⟩
end Theory.SpecificGroups.SymplecticFour.NondefiningPrimeActors
