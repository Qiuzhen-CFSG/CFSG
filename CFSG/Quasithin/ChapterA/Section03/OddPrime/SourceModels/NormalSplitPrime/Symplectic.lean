module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.Quartic
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import GorensteinWalter.PSL2Cardinality

/-!
# The full symplectic field-actor exclusion

For an odd prime of rank two in Sp₄(q), the cyclic fourth-cyclotomic Sylow
calculation forces p to divide q²−1. Fixed-point counting for an order-p
coefficient automorphism preserves this divisibility in its literal fixed
field. Two orthogonal SL₂ factors over that field supply a fixed elementary
group of order p², including primes dividing q+1. Together with the outside
field actor its faithful inner image has rank three. The actual inner–field
decomposition therefore excludes every original outside order-p actor.

The final theorem applies this calculation after H/O₂(H), preserving the
component central quotient and its prime-to-p center. No split-torus or
fixed-rank hypothesis remains. Source: Aschbacher–Smith A.3.18, pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms

private theorem fixed_card_modEq {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (σ : F ≃+* F) (hσ : orderOf σ = p) :
    Nat.card F ≡ Nat.card (FieldFixedResidual.fixedField σ) [MOD p] := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hσ, pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield P F) [MOD p] at hc
  have hK : FixedPoints.subfield P F = FieldFixedResidual.fixedField σ := by
    ext x
    rw [FieldFixedResidual.mem_fixedField]
    change (∀ g : P, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rwa [hK] at hc

private theorem symplectic_elementary_of_quadratic {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card SL(2,F) by
      rw [GorensteinWalter.sl2_card_formula]
      exact dvd_mul_of_dvd_right hd _)
  let P := zpowers a
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let f : P × P →* Sp F :=
    CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom.comp
      (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom_injective he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

private theorem symplectic_fixed_elementary {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (fieldAutomorphism σ).fixedSubgroup := by
  have hc := (fixed_card_modEq σ hσ).pow 2
  have hs := Nat.ModEq.sub_right (a := 1)
    (Nat.one_le_pow _ _ Nat.card_pos) (Nat.one_le_pow _ _ Nat.card_pos) hc
  have hdK : p ∣ Nat.card (FieldFixedResidual.fixedField σ) ^ 2 - 1 :=
    Nat.modEq_zero_iff_dvd.mp (hs.symm.trans hd.modEq_zero_nat)
  obtain ⟨B, hB, hcard⟩ := symplectic_elementary_of_quadratic hdK
  let := hB
  let f : Sp (FieldFixedResidual.fixedField σ) →* Sp F :=
    (fieldAutomorphism σ).fixedSubgroup.subtype.comp
      (FieldFixedResidual.fixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAutomorphism σ).fixedSubgroup.subtype_injective.comp
      (FieldFixedResidual.fixedEquiv σ).symm.injective
  refine ⟨B.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [card_map_of_injective hf, hcard]
  · rintro _ ⟨b, _, rfl⟩
    exact ((FieldFixedResidual.fixedEquiv σ).symm b).property

private theorem symplectic_field_rank_three {F : Type*} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAutomorphism σ ∈ A)
    (hd : p ∣ Nat.card F ^ 2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := symplectic_fixed_elementary σ hσ hd
  let := hE
  let f : Sp F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact InvolutionNormalForms.inner_injective (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAutomorphism σ, hσA⟩
  have hfield : Function.Injective (fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAutomorphismHom hfield σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g, _, he⟩
    have hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) :=
      ⟨g, congrArg Subtype.val he⟩
    have hs := InvolutionNormalForms.field_eq_one_of_inner σ hi
    rw [hs, orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAutomorphism σ y * g⁻¹ = fieldAutomorphism σ (g * y * g⁻¹)
    rw [map_mul, map_mul, map_inv, hgfix]
  have hcB : Nat.card B = p ^ 2 := by rw [card_map_of_injective hf, hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

private theorem symplectic_prime_actor_inner {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : 1 < primeRank p (Sp F))
    (A : Subgroup (MulAut (Sp F))) (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut (Sp F)) (haA : a ∈ A) (ha : a ^ p = 1) :
    a ∈ MulAut.innerSubgroup (Sp F) := by
  have hd : p ∣ Nat.card F ^ 2 - 1 := by
    by_contra hn
    let P : Sylow p (Sp F) := default
    have hb := P.primeRank_le_one_of_isCyclic
      (CentralCovers.OddPrimary.sylow_isCyclic_of_not_dvd_sq_sub_one
        (by rintro rfl; exact (by decide : ¬ Odd 2) ho) hn P)
    omega
  obtain ⟨g, σ, he, hσ⟩ := OddFieldActors.inner_field_of_primePower hF ho a
    (m := 1) (by simpa only [pow_one] using ha)
  have hσA : fieldAutomorphism σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g, rfl⟩)) haA
    rwa [he, inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hpσ : orderOf σ = p := orderOf_eq_prime
      (by simpa only [pow_one] using hσ) hn
    have hb := symplectic_field_rank_three A hinner σ hpσ hσA hd
    omega
  rw [he, hσone]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := fieldAutomorphismHom.map_one
  rw [hh, mul_one]
  exact ⟨g, rfl⟩

/-- The ordinary symplectic row admits no outside odd-prime actor under SQTK. -/
theorem ordinary_not_symplectic_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    omega
  let e := e₀.trans EvenProjective.equiv.symm
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  apply outside_action_not_inner hz hr hb e a ha haK
  apply symplectic_prime_actor_inner hlarge ho (by rwa [central_model_rank hz e]) f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
  have hapow : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  rw [← map_pow, hapow, map_one]

/-- Eliminate the symplectic row on the literal two-core quotient. -/
theorem not_symplectic_twoCore_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) 2 (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_not_symplectic_model (twoCore_sqtk hH) hp ho hr' hz' hn
    (hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
