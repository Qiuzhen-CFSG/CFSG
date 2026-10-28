module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.ShortBlock
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import GorensteinWalter.PSL2Cardinality

/-!
# Noncubic field actors of the characteristic-two G₂ component

For p > 3, the cyclic cyclotomic Sylow calculation forces a rank-two prime
to divide q²−1. Fixed-point counting preserves this divisibility in the
literal coefficient fixed field. The faithful pair of SL₂ factors gives
an elementary p² subgroup there. Its inner image and the outside field
actor violate SQTK. In degree two, the field automorphism order already
excludes every such prime; no large-field assumption is added to the row.

The full actual inner–field description is applied to the original
order-p actor, and the two-core application retains the component marking
and its p-prime center. Source: Aschbacher–Smith A.3.18, printed pp.51–53;
GLS3 §2.5 and the intrinsic G₂ cyclotomic Sylow calculations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions

private theorem g2_elementary_of_quadratic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
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
  let f : P × P →* Model F :=
    MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom.comp
      (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom_injective he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

private theorem g2_fixed_elementary {F : Type*} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (fieldAction σ).fixedSubgroup := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hσ, pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (EvenFieldFixedResidual.fixedField σ) [MOD p] at hc
  have hc := hc.pow 2
  have hs := Nat.ModEq.sub_right (a := 1)
    (Nat.one_le_pow _ _ Nat.card_pos) (Nat.one_le_pow _ _ Nat.card_pos) hc
  have hdK : p ∣ Nat.card (EvenFieldFixedResidual.fixedField σ) ^ 2 - 1 :=
    Nat.modEq_zero_iff_dvd.mp (hs.symm.trans hd.modEq_zero_nat)
  obtain ⟨B, hB, hcard⟩ := g2_elementary_of_quadratic hdK
  let := hB
  let f : Model (EvenFieldFixedResidual.fixedField σ) →* Model F :=
    (fieldAction σ).fixedSubgroup.subtype.comp
      (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAction σ).fixedSubgroup.subtype_injective.comp
      (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.injective
  refine ⟨B.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [card_map_of_injective hf, hcard]
  · rintro _ ⟨b, _, rfl⟩
    exact ((EvenFieldFixedResidual.coefficientFixedEquiv σ).symm b).property

private theorem g2_field_rank_three {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) {p : ℕ} [Fact p.Prime] (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAction σ ∈ A)
    (hd : p ∣ Nat.card F ^ 2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := g2_fixed_elementary σ hσ hd
  let := hE
  let f : Model F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hF))
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAction σ, hσA⟩
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAction fieldAction_injective σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g, _, he⟩
    have hi : fieldAction σ ∈ MulAut.innerSubgroup (Model F) :=
      ⟨g, congrArg Subtype.val he⟩
    obtain ⟨u, hu⟩ := hi
    have hs := fieldAction_eq_conj_implies_one σ u hu.symm
    rw [hs, orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAction σ y * g⁻¹ = fieldAction σ (g * y * g⁻¹)
    rw [map_mul, map_mul, map_inv, hgfix]
  have hcB : Nat.card B = p ^ 2 := by rw [card_map_of_injective hf, hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

private theorem g2_prime_actor_inner {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hr : 1 < primeRank p (Model F))
    (A : Subgroup (MulAut (Model F))) (hinner : MulAut.innerSubgroup (Model F) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut (Model F)) (haA : a ∈ A) (ha : a ^ p = 1) :
    a ∈ MulAut.innerSubgroup (Model F) := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    omega
  obtain ⟨g, σ, he⟩ := exists_inner_field hlarge a
  have hσ : σ ^ p = 1 := by
    have hh := congrArg (fieldComponent hlarge) ha
    rw [map_pow, he, fieldComponent_inner_field, map_one] at hh
    exact hh
  have hσA : fieldAction σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g, rfl⟩)) haA
    rwa [he, inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hnσ
    have hpσ : orderOf σ = p := orderOf_eq_prime hσ hnσ
    have hbig : 4 < Nat.card F := by
      by_cases hn2 : n = 2
      · have hs := FiniteField.ringAut_sq_of_card_prime_pow Nat.prime_two
          (by decide : 2 ≤ 2) (hn2 ▸ hF) σ
        have hd := orderOf_dvd_of_pow_eq_one hs
        rw [hpσ] at hd
        have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
        omega
      · rw [hF]
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ n by omega)
        omega
    have hd : p ∣ Nat.card F ^ 2 - 1 := by
      by_contra hquad
      have horder : p ∣ Nat.card (Model F) := by
        by_contra hnot
        have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
        omega
      let P : Sylow p (Model F) := default
      have hb := P.primeRank_le_one_of_isCyclic
        (MultiplierOrdinary.Nondefining.CyclotomicSylow.sylow_isCyclic
          hbig hp3 hquad horder P)
      omega
    have hb := g2_field_rank_three hlarge A hinner σ hpσ hσA hd
    omega
  rw [he, hσone, map_one, mul_one]
  exact ⟨g, rfl⟩

/-- The ordinary binary G₂ row has no outside noncubic prime actor under SQTK. -/
theorem ordinary_not_g2_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At (K ⧸ center K) (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e := e₀
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  apply outside_action_not_inner hz hr hb e a ha haK
  have hpgt : 3 < p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  apply g2_prime_actor_inner hn hF hpgt (by rwa [central_model_rank hz e]) f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
  have hapow : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  rw [← map_pow, hapow, map_one]

/-- The same exclusion on the actual two-core component of the split extension. -/
theorem not_g2_twoCore_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_not_g2_model (twoCore_sqtk hH) hp ho hp3 hr' hz' hn
    (hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
