module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalSplit
public import Theory.SpecificGroups.Triality.QuadraticTori.OrthogonalRankOne
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LeviSemilinear.Coefficients
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve

/-!
# Fixed quadratic subsystems for the triality branch of A.3.18

An order-p coefficient automorphism restricts to the original q-element base
field. Fixed-point counting makes the size of its fixed field congruent to q
modulo p. Thus p dividing q² - 1 supplies an order-p element in SL₂ over that
fixed field. Two copies embed in the faithful orthogonal SL₂(q³) × SL₂(q)
subsystem of the genuine triality carrier. Equivariance of the pinned maps,
the highest-root Weyl word, and the elementary central quotient proves that
this elementary p-square is fixed by that same coefficient actor.

Its faithful inner image and the disjoint outside order-p actor give rank
three, contradicting the inherited SQTK bound. The original ambient action
and literal two-core quotient then exclude every quadratic triality prime.
For the remaining triality row, the actual coefficient order forces p to
divide the original exponent n. The cyclic twelfth-cyclotomic Sylow theorem
leaves only the third and sixth cyclotomic factors. The refinement is applied
to the literal Cartan extension in OrdinaryRootFF.OddRankSource.

The Ree nonsplit primes, the remaining triality cyclotomic primes, and the
outer cubic-cover diagonal clauses remain explicit source obligations.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.6, p.615.
The orthogonal subsystem uses GLS3 §2.6, Proposition 2.6.2(a,b); the imported
triality modules record its explicit root, field, and quotient constructions.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
open Matrix
open scoped MatrixGroups
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.Parabolics
open Triality.Standard.ParabolicOuterTwo Triality.Standard.QuadraticTori.OrthogonalRankOne
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
namespace TrialityQuadratic

private theorem map_transvection {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single i j t) f = 1 + Matrix.single i j (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

private theorem coefficient_pinned (P : Parameters) (D : PinnedRankOneMaps P)
    (e : CoefficientAut P) (i : Fin 4) (g : SL(2, ExtensionField P)) :
    coefficientSplit P e (D.hom i g) =
      D.hom i (SpecialLinearGroup.map e.toRingHom g) := by
  apply sl2_root_induction (fun g => coefficientSplit P e (D.hom i g) =
    D.hom i (SpecialLinearGroup.map e.toRingHom g)) ?_ ?_ ?_ g
  · intro t
    exact (congrArg (coefficientSplit P e) (D.positive i t)).trans
      ((coefficient_positiveRoot P e i t).trans
        ((D.positive i (e t)).symm.trans
          (congrArg (D.hom i) (map_transvection e.toRingHom (by decide : (0 : Fin 2) ≠ 1) t).symm)))
  · intro t
    exact (congrArg (coefficientSplit P e) (D.negative i t)).trans
      ((coefficient_negativeRoot P e i t).trans
        ((D.negative i (e t)).symm.trans
          (congrArg (D.hom i) (map_transvection e.toRingHom (by decide : (1 : Fin 2) ≠ 0) t).symm)))
  · intro g h hg hh
    simp only [map_mul, hg, hh]

private theorem coefficient_armsEmbedding (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (e : CoefficientAut P) (g : SL(2, ExtensionField P)) :
    coefficientSplit P e (D.armsFixedEmbedding C g) =
      D.armsFixedEmbedding C (SpecialLinearGroup.map e.toRingHom g) := by
  have hF (g : SL(2, ExtensionField P)) :
      SpecialLinearGroup.map e.toRingHom (sl2Frobenius P g) =
        sl2Frobenius P (SpecialLinearGroup.map e.toRingHom g) := by
    ext i j
    exact Coverage.coefficient_frobenius P e (g i j)
  change coefficientSplit P e
      (D.hom 0 g * D.hom 2 (sl2Frobenius P g) *
        D.hom 3 (sl2Frobenius P (sl2Frobenius P g))) = _
  simp only [map_mul, coefficient_pinned, hF]
  rfl


private theorem map_conjugate_of_fixed {G : Type*} [Group G]
    (α : MulAut G) (w x y : G) (hw : α w = w) (hx : α x = y) :
    α (w * x * w⁻¹) = w * y * w⁻¹ := by
  rw [map_mul, map_mul, map_inv, hw, hx]

private theorem coefficient_highestEmbedding (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (g : SL(2, GaloisField P.prime P.exponent)) :
    coefficientSplit P e (highestBaseEmbedding P hp g) =
      highestBaseEmbedding P hp (SpecialLinearGroup.map (coefficientBaseField P e).toRingHom g) := by
  have hw : coefficientSplit P e (wordElement P [1, 0, 2, 3]) =
      wordElement P [1, 0, 2, 3] := by
    simp only [wordElement, weylWord, map_mul, map_one,
      coefficient_positiveRoot, coefficient_negativeRoot, map_neg, map_inv₀]
  have he : coefficientSplit P e ((pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P g)) =
      (pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P
        (SpecialLinearGroup.map (coefficientBaseField P e).toRingHom g)) := by
    refine (coefficient_pinned P (pinnedRankOneMaps P hp) e 1 (sl2BaseEmbedding P g)).trans ?_
    apply congrArg ((pinnedRankOneMaps P hp).hom 1)
    ext i j
    exact (coefficientBaseField_embedding P e (g i j)).symm
  exact map_conjugate_of_fixed (coefficientSplit P e) (wordElement P [1,0,2,3]) _ _ hw he

private theorem coefficient_carrier_lift {F : Type*} [Field F] [CharP F 2]
    (P : Parameters) (hp : P.prime = 2) (f : SL(2,F) →* fixedSubgroup P)
    (e : CoefficientAut P) (s : SL(2,F) →* SL(2,F))
    (he : ∀ g, coefficientFixed P e (f g) = f (s g)) (g : SL(2,F)) :
    coefficientAction P e (toCarrier P (sl2ElementaryLift P hp f g)) =
      toCarrier P (sl2ElementaryLift P hp f (s g)) := by
  exact (coefficientCarrier_toCarrier P e (sl2ElementaryLift P hp f g)).trans
    (congrArg (toCarrier P) (Subtype.ext (he g)))

private theorem coefficient_armsCarrier (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (g : SL(2, ExtensionField P)) :
    coefficientAction P e (armsCarrierEmbedding P hp g) =
      armsCarrierEmbedding P hp (SpecialLinearGroup.map e.toRingHom g) := by
  let := rankOneExtensionCharTwo P hp
  exact coefficient_carrier_lift P hp (armsFixedMap P hp) e
    (SpecialLinearGroup.map e.toRingHom)
    (fun g => Subtype.ext (coefficient_armsEmbedding P _ _ e g)) g

private theorem coefficient_highestCarrier (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (g : SL(2, GaloisField P.prime P.exponent)) :
    coefficientAction P e (highestCarrierEmbedding P hp g) =
      highestCarrierEmbedding P hp
        (SpecialLinearGroup.map (coefficientBaseField P e).toRingHom g) := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  exact coefficient_carrier_lift P hp (highestFixedMap P hp) e
    (SpecialLinearGroup.map (coefficientBaseField P e).toRingHom)
    (fun g => Subtype.ext (coefficient_highestEmbedding P hp e g)) g

private theorem coefficientBaseField_pow (P : Parameters) (σ : CoefficientAut P)
    {p : ℕ} (hσ : σ ^ p = 1) : coefficientBaseField P σ ^ p = 1 := by
  have hi (n : ℕ) (t : GaloisField P.prime P.exponent) :
      baseFieldEmbedding P ((coefficientBaseField P σ ^ n) t) =
        (σ ^ n) (baseFieldEmbedding P t) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change baseFieldEmbedding P (coefficientBaseField P σ ((coefficientBaseField P σ ^ n) t)) =
        σ ((σ ^ n) (baseFieldEmbedding P t))
      rw [coefficientBaseField_embedding, ih]
  apply RingEquiv.ext
  intro t
  apply (baseFieldEmbedding P).injective
  change baseFieldEmbedding P ((coefficientBaseField P σ ^ p) t) = baseFieldEmbedding P t
  exact (hi p t).trans (DFunLike.congr_fun hσ (baseFieldEmbedding P t))

private theorem fixed_card_modEq {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (σ : F ≃+* F) (hσ : σ ^ p = 1) :
    Nat.card F ≡ Nat.card (FixedBy.subfield F σ) [MOD p] := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hσ)
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield P F) [MOD p] at hc
  have he : FixedPoints.subfield P F = FixedBy.subfield F σ := by
    ext x
    change (∀ g : P, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rwa [he] at hc

private theorem sl2_map_injective {F K : Type*} [Field F] [Field K] (f : F →+* K) :
    Function.Injective (SpecialLinearGroup.map (n := Fin 2) f) := by
  intro x y h
  ext i j
  exact f.injective (congrArg (fun g : SL(2,K) => g i j) h)

/-- The actual coefficient actor fixes a rank-two elementary subgroup at every
quadratic prime, including the nonsplit primes dividing q + 1. -/
theorem exists_fixed_elementary (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : σ ^ p = 1) :
    ∃ E : Subgroup (BinaryCarrier n hn), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (coefficientAction (binaryParameters n hn) σ).fixedSubgroup := by
  let P := binaryParameters n hn
  have hpP : P.prime = 2 := rfl
  let β := coefficientBaseField P σ
  let F := FixedBy.subfield (GaloisField P.prime P.exponent) β
  have hc := (fixed_card_modEq β (coefficientBaseField_pow P σ hσ)).pow 2
  have hs := Nat.ModEq.sub_right (a := 1)
    (Nat.one_le_pow _ _ Nat.card_pos) (Nat.one_le_pow _ _ Nat.card_pos) hc
  have hdF : p ∣ Nat.card F ^ 2 - 1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    apply hs.symm.trans
    rw [card_baseField]
    exact hd.modEq_zero_nat
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card SL(2,F) by
      rw [GorensteinWalter.sl2_card_formula]
      exact dvd_mul_of_dvd_right hdF _)
  let C := zpowers a
  let : IsElementaryAbelian p C := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (C × C) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.2) }
  let b : SL(2,F) →* SL(2, GaloisField P.prime P.exponent) := SpecialLinearGroup.map F.subtype
  let c := (sl2BaseEmbedding P).comp b
  let j : C × C →* SL(2,ExtensionField P) × SL(2,GaloisField P.prime P.exponent) :=
    (c.comp C.subtype).prodMap (b.comp C.subtype)
  let f := (productEmbedding P hpP).comp j
  have hb : Function.Injective b := sl2_map_injective F.subtype
  have hj : Function.Injective j := by
    intro x y hh
    apply Prod.ext
    · exact Subtype.ext (hb (sl2BaseEmbedding_injective P (congrArg Prod.fst hh)))
    · exact Subtype.ext (hb (congrArg Prod.snd hh))
  have hf : Function.Injective f := (productEmbedding_injective P hpP).comp hj
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range, inferInstance, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_prod, Nat.card_zpowers, ha, pow_two]
  · rintro _ ⟨⟨x,y⟩, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hbfix (g : SL(2,F)) : SpecialLinearGroup.map β.toRingHom (b g) = b g := by
      ext i j
      exact (g i j).property
    have hcfix (g : SL(2,F)) : SpecialLinearGroup.map σ.toRingHom (c g) = c g := by
      ext i j
      change σ (baseFieldEmbedding P ((g i j).val)) = baseFieldEmbedding P ((g i j).val)
      rw [← coefficientBaseField_embedding]
      exact congrArg (baseFieldEmbedding P) (g i j).property
    change coefficientAction P σ
      (armsCarrierEmbedding P hpP (c x.val) * highestCarrierEmbedding P hpP (b y.val)) = _
    rw [map_mul, coefficient_armsCarrier, coefficient_highestCarrier, hcfix, hbfix]
    rfl

/-- The fixed quadratic subsystem and a noninner coefficient actor give an elementary
subgroup of rank three in the literal automorphism overgroup. -/
theorem field_actor_rank_three (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (A : Subgroup (MulAut (BinaryCarrier n hn)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ A)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p)
    (hb : orderOf (coefficientAction _ σ) = p)
    (hbA : coefficientAction _ σ ∈ A)
    (hout : coefficientAction _ σ ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_elementary n hn hd σ (hσ ▸ pow_orderOf_eq_one σ)
  let := hE
  let b := coefficientAction (binaryParameters n hn) σ
  let f : BinaryCarrier n hn →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect)
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨b, hbA⟩
  have hx : orderOf x = p :=
    (orderOf_injective A.subtype A.subtype_injective x).symm.trans hb
  have hxB : x ∉ B := by
    rintro ⟨g, _, he⟩
    exact hout ⟨g, congrArg Subtype.val he⟩
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * b y * g⁻¹ = b (g * y * g⁻¹)
    rw [map_mul, map_mul, map_inv, hgfix]
  have hcB : Nat.card B = p ^ 2 := by rw [card_map_of_injective hf, hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every prime actor at a quadratic prime is inner in a rank-two
full-inner automorphism overgroup of the genuine triality model. -/
theorem prime_actor_inner (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (A : Subgroup (MulAut (BinaryCarrier n hn)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut (BinaryCarrier n hn)) (haA : a ∈ A)
    (ha : a ^ p = 1) : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn) := by
  by_contra hout
  have haorder : orderOf a = p := orderOf_eq_prime ha
    (fun he => hout (he ▸ (MulAut.innerSubgroup _).one_mem))
  let φ := coefficientAction (binaryParameters n hn)
  have hfaithful : Function.Injective
      ((QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))).comp φ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    exact (EvenField.NormalForm.coefficientAction_mem_inner_iff n hn σ).mp
      ((QuotientGroup.eq_one_iff _).mp hσ)
  obtain ⟨g, σ, _, hσ, hσA, hb, houter⟩ := MulAut.exists_prime_coefficient_in_overgroup
    φ hfaithful (Coverage.binary_inner_coefficient n hn) A hinner a haA haorder hout
  have hh := field_actor_rank_three n hn hd A hinner σ hσ hb hσA houter
  omega

end TrialityQuadratic

variable {H : Type*} [Group H] [Finite H]

/-- Exclude the ordinary triality row at a quadratic prime using the
actual outside actor and inherited SQTK rank bound. -/
theorem ordinary_not_triality_quadratic_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 1 ≤ n) (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := hn
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hmodel
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n hn0) :=
    e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n hn0) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  apply outside_action_not_inner hz hr hb e a ha haK
  apply TrialityQuadratic.prime_actor_inner n hn0 hd f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
  rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]

/-- Transport the triality quadratic-prime exclusion to the literal two-core
component, preserving the actual quotient image of the outside actor. -/
theorem not_triality_quadratic_twoCore_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 1 ≤ n) (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_not_triality_quadratic_model (twoCore_sqtk hH) hp ho hr' hz' hn hd
    (hmodel.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2


private theorem triality_cyclotomic_of_rank (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hr : 1 < primeRank p (BinaryCarrier n hn))
    (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1) :
    p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
  have hd : p ∣ Nat.card (BinaryCarrier n hn) := by
    by_contra hnot
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
    omega
  rcases Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.dvd_cyclotomic_of_dvd_card
    hn hp hquad hd with h3 | h6 | h12
  · exact Or.inl h3
  · exact Or.inr h6
  · let Q : Sylow p (BinaryCarrier n hn) := default
    have hb := Q.primeRank_le_one_of_isCyclic
      (Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.isCyclic_sylow
        n hn (by omega) h12 Q)
    omega

private theorem ordinary_triality_parameters
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 1 ≤ n) (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    p ∣ n ∧ (p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := hn
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hmodel
  let : IsSimpleGroup (BinaryCarrier n hn0) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect (BinaryCarrier n hn0) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hpgt : 3 < p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  have hrS : 1 < primeRank p (BinaryCarrier n hn0) := by rwa [central_model_rank hz e]
  refine ⟨?_, triality_cyclotomic_of_rank n hn0 hpgt hrS hquad⟩
  let f := normalAction K e
  have hout := outside_action_not_inner hz hr (hH.stronglyQuasithin p hp ho) e a ha haK
  have hinner : MulAut.innerSubgroup (BinaryCarrier n hn0) ≤ f.range := by
    rw [← normalAction_component_image K e]
    exact Subgroup.map_le_range f K
  have hfa : (f a) ^ p = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hforder : orderOf (f a) = p := orderOf_eq_prime hfa
    (fun he => hout (he ▸ (MulAut.innerSubgroup _).one_mem))
  let φ := coefficientAction (binaryParameters n hn0)
  have hfaithful : Function.Injective
      ((QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn0))).comp φ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    exact (EvenField.NormalForm.coefficientAction_mem_inner_iff n hn0 σ).mp
      ((QuotientGroup.eq_one_iff _).mp hσ)
  obtain ⟨g, σ, _, hσ, _, _, _⟩ := MulAut.exists_prime_coefficient_in_overgroup
    φ hfaithful (Coverage.binary_inner_coefficient n hn0) f.range hinner (f a) ⟨a, rfl⟩ hforder hout
  have hc : Nat.card (CoefficientAut (binaryParameters n hn0)) = 3 * n :=
    GaloisField.card_ringAut 2 (3 * n) (by omega)
  have hd := orderOf_dvd_natCard σ
  rw [hσ, hc] at hd
  exact hp.dvd_mul.mp hd |>.resolve_left
    (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))

/-- An actual exceptional noncubic actor retains its original field degree:
p divides n, and after the quadratic exclusion only the third and sixth
cyclotomic factors can support rank two. -/
theorem triality_twoCore_parameters
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 1 ≤ n) (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    p ∣ n ∧ (p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_triality_parameters (twoCore_sqtk hH) hp ho hp3 hr' hz' hn hquad
    (hmodel.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

open Chapter1.Section02.LocalModels

/-- Exceptional models after excluding all triality quadratic primes and
Ree split primes. No fixed-point hypothesis is added to either model. -/
def RefinedNonsplitModel (p : ℕ) (S : Type*) [Group S] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ p ∣ n ∧ ¬ p ∣ (2 ^ n) ^ 2 - 1 ∧
    (p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) ∧
    Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ¬ p ∣ 2 ^ (2 * m + 1) - 1 ∧ IsReeF4At S m)

/-- The unresolved exceptional and outer-cover branches on the literal
component and the original outside actor. -/
def RefinedNonsplitOrCoverRemainder (p : ℕ) (K : Subgroup H) (a : H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    RefinedNonsplitModel p ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ OuterCubicCoverActor (twoCoreComponent K) (QuotientGroup.mk' (pCore 2 H) a))

/-- Apply the fixed quadratic subsystem to the original split extension.
The triality primes dividing q + 1 are discharged without changing its actor. -/
theorem alternatives_or_refined_nonsplit_or_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ RefinedNonsplitOrCoverRemainder p K a := by
  rcases alternatives_or_nonsplit_or_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3, hz, hm⟩ | hcover
  · apply Or.inr
    apply Or.inl
    refine ⟨hp3, hz, ?_⟩
    rcases hm with ⟨n, hn, _, hm⟩ | hree
    · have hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1 := fun hd =>
        not_triality_quadratic_twoCore_model hH hK hp ho hr hz hn hd hm a ha haK
      have hparam := triality_twoCore_parameters hH hK hp ho hp3 hr hz hn hquad hm a ha haK
      exact Or.inl ⟨n, hn, hparam.1, hquad, hparam.2, hm⟩
    · exact Or.inr hree
  · exact Or.inr (Or.inr hcover)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
