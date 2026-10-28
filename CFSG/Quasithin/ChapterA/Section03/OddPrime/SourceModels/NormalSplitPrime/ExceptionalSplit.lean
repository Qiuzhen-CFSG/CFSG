module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverOuter
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus
public import Theory.SpecificGroups.ReeF4.PrimeFieldRepresentative

/-!
# Fixed split tori in the exceptional field rows of A.3.18

For a prime p dividing q - 1, an order-p coefficient actor fixes the
p-torsion in each coordinate of the actual rank-two split torus. On a
cyclic coordinate this follows from Fermat's congruence: if the actor is
raising to k, its p-th power is raising to k^p, which agrees with k on
p-torsion. The Ree calculation uses its literal canonical Frobenius;
the triality calculation uses the four original coroot words and the
genuine graph-field fixed elementary central quotient.

Faithfulness of the inner image and disjointness from the outside actor
then give an elementary subgroup of rank three. The normal component
action and literal two-core transports contradict the source SQTK bound.
The resulting source reduction is applied to the original Cartan extension
in OrdinaryRootFF.OddRankSource. Exceptional primes outside the split torus
and outer actors on central cubic covers remain explicit obligations.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.6, p.615.
The concrete torus and coefficient-action sources are recorded in the
imported Ree and triality modules.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeSplit

private theorem fixed_of_prime_power_action {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (α : MulAut G) (hα : α ^ p = 1)
    (x : G) (hx : x ^ p = 1) (k : ℕ) (hk : α x = x ^ k) : α x = x := by
  have hi (n : ℕ) : (α ^ n) x = x ^ (k ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow, hk, ← pow_mul, pow_succ']
  have he : x ^ (k ^ p) = x := by simpa only [hα, MulAut.one_apply] using (hi p).symm
  have hc : k ^ p ≡ k [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow] using ZMod.pow_card (k : ZMod p)
  have hp : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have hh : x ^ (k ^ p) = x ^ k := pow_eq_pow_iff_modEq.mpr (hc.of_dvd hp)
  exact hk.trans (hh.symm.trans he)

private theorem elementary_pair {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    ∃ E : Subgroup (Fˣ × Fˣ), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card Fˣ by rwa [Nat.card_units])
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
  let f := P.subtype.prodMap P.subtype
  have hf : Function.Injective f := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

open ReeF4 ReeF4.ConverseParabolics.FullLeviRepresentation

/-- Every order-p canonical field actor fixes the p-torsion of the actual split torus. -/
theorem exists_fixed_elementary {m p : ℕ} [Fact p.Prime]
    (d : LocalBlockInput m) (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (b : MulAut d.fixedGroup) (hb : orderOf b = p)
    (hbField : b ∈ zpowers d.fieldAutomorphism) :
    ∃ E : Subgroup d.fixedGroup, IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ b.fixedSubgroup := by
  obtain ⟨B, hB, hcB⟩ := elementary_pair
    (show p ∣ Nat.card (CoefficientField m) - 1 by rwa [field_card])
  let := hB
  let f : (CoefficientField m)ˣ × (CoefficientField m)ˣ →* d.fixedGroup :=
    d.modelEquiv.symm.toMonoidHom.comp (torusHom m)
  have hf : Function.Injective f := d.modelEquiv.symm.injective.comp (torusHom_injective m)
  have hfT (x : (CoefficientField m)ˣ × (CoefficientField m)ˣ) : f x ∈ Cartan.torus d := by
    have ht := torusElement_mem x.1 x.2
    change toSplitGroup m (torusHom m x) ∈ Parabolics.splitTorus m at ht
    rw [Parabolics.splitTorus_eq_diagonalTorus] at ht
    change (f x).val ∈ Parabolics.diagonalTorus m
    have he : (f x).val = toSplitGroup m (torusHom m x) := by
      have hh := (d.modelEquiv_coe (f x)).symm
      simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, toSplitGroup_apply] using hh
    rwa [he]
  obtain ⟨k, hk⟩ := Cartan.field_subgroup_torus_power d b hbField
  refine ⟨B.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [card_map_of_injective hf, hcB]
  · rintro _ ⟨x, hx, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply fixed_of_prime_power_action b (hb ▸ pow_orderOf_eq_one b) (f x)
      (show (f x) ^ p = 1 from ?_) (2 ^ k) (hk _ (hfT x))
    have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p B) (⟨x, hx⟩ : B)
    have hxp : x ^ p = 1 := congrArg Subtype.val hp
    rw [← map_pow, hxp, map_one]

/-- The faithful inner image of the fixed torus and the outside field actor have rank three. -/
theorem field_actor_rank_three {m p : ℕ} [Fact p.Prime]
    (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (A : Subgroup (MulAut d.fixedGroup)) (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (b : MulAut d.fixedGroup) (hb : orderOf b = p)
    (hbField : b ∈ zpowers d.fieldAutomorphism) (hbA : b ∈ A) :
    3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_elementary d hd b hb hbField
  let := hE
  let f : d.fixedGroup →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
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
    have hi : b ∈ MulAut.innerSubgroup d.fixedGroup := ⟨g, congrArg Subtype.val he⟩
    have hbone := Subgroup.disjoint_def.mp (Cartan.field_disjoint_innerDiagonal d)
      hbField (Cartan.inner_le_innerDiagonal d hi)
    rw [hbone, orderOf_one] at hb
    exact (Fact.out : p.Prime).ne_one hb.symm
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

/-- A noninner prime actor is impossible at a split-torus prime. -/
theorem prime_actor_inner {m p : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (A : Subgroup (MulAut d.fixedGroup)) (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut d.fixedGroup) (haA : a ∈ A)
    (ha : a ^ p = 1) : a ∈ MulAut.innerSubgroup d.fixedGroup := by
  by_contra hout
  have haorder : orderOf a = p := orderOf_eq_prime ha (fun he =>
    hout (he ▸ (MulAut.innerSubgroup d.fixedGroup).one_mem))
  obtain ⟨_, g, σ, _, _, hσA, hσ, _⟩ :=
    LocalBlockInput.exists_prime_field_representative hm d A hinner a haA haorder hout
  have hh := field_actor_rank_three d hd A hinner σ.val hσ σ.property hσA
  omega

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeSplit

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

variable {H : Type*} [Group H] [Finite H]

/-- The ordinary quasisimple Ree row cannot admit an outside actor at a split-torus prime. -/
theorem ordinary_not_ree_split_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {m : ℕ} (hm : 1 ≤ m) (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup d.fixedGroup := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let f := normalAction K e
  have hb := hH.stronglyQuasithin p hp ho
  have hout := outside_action_not_inner hz hr hb e a ha haK
  have hfa : (f a) ^ p = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  exact hout (ReeSplit.prime_actor_inner hm d hd f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩ hfa)

/-- The same exclusion on the original component's literal two-core quotient. -/
theorem not_ree_split_twoCore_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {m : ℕ} (hm : 1 ≤ m) (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At
      ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) m)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  exact ordinary_not_ree_split_model (twoCore_sqtk hH) hp ho hr' hz' hm hd
    ⟨d, ⟨(centralQuotientEquiv (twoCoreComponentEquiv hK)).trans e⟩⟩
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

private theorem prime_aut_fixes_cyclic_torsion {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {p : ℕ} [Fact p.Prime] (α : MulAut C) (hα : α ^ p = 1)
    (x : C) (hx : x ^ p = 1) : α x = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := C)
  obtain ⟨k, hk⟩ := hg (α g)
  have hpower (y : C) : α y = y ^ k := by
    obtain ⟨n, rfl⟩ := hg y
    rw [map_pow, ← hk, pow_right_comm]
  exact ReeSplit.fixed_of_prime_power_action α hα x hx k (hpower x)

namespace TrialitySplit
open Triality.Standard Triality.Standard.OuterOdd
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.TorusCoordinates

private theorem coefficient_fixes_unit {p : ℕ} [Fact p.Prime]
    (P : Parameters) (σ : CoefficientAut P) (hσ : σ ^ p = 1)
    (t : (ExtensionField P)ˣ) (ht : t ^ p = 1) : Units.map σ.toMonoidHom t = t := by
  let α : MulAut (ExtensionField P)ˣ := Units.mapEquiv σ.toMulEquiv
  have hα : α ^ p = 1 := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    have hi (n : ℕ) : ((α ^ n) u).val = (σ ^ n) u.val := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', MulAut.mul_apply]
        change σ (((α ^ n) u).val) = σ ((σ ^ n) u.val)
        rw [ih]
    rw [hi, hσ]
    rfl
  exact prime_aut_fixes_cyclic_torsion α hα t ht

private theorem coefficient_word (P : Parameters) (σ : CoefficientAut P)
    (i : Fin 4) (t : (ExtensionField P)ˣ) :
    coefficientSplit P σ (torusWord P i t) =
      torusWord P i (Units.map σ.toMonoidHom t) := by
  have hpos (i : Fin 4) (t : ExtensionField P) :
      coefficientSplit P σ (positiveRoot P i t) = positiveRoot P i (σ t) :=
    coefficientSplit_positive P σ _ t
  have hneg (i : Fin 4) (t : ExtensionField P) :
      coefficientSplit P σ (negativeRoot P i t) = negativeRoot P i (σ t) :=
    coefficientSplit_negative P σ _ t
  simp only [torusWord, weylWord, map_mul, hpos, hneg, map_neg, map_inv₀, map_one]
  rfl

private theorem fixed_image_of_split_fixed (P : Parameters) (σ : CoefficientAut P)
    (x : elementarySubgroup P)
    (hx : coefficientSplit P σ (elementaryInclusion P x) = elementaryInclusion P x) :
    coefficientCarrier P σ (toCarrier P x) = toCarrier P x := by
  have he : coefficientElementary P σ x = x := Subtype.ext (Subtype.ext hx)
  exact (coefficientCarrier_toCarrier P σ x).trans (congrArg (toCarrier P) he)

private theorem fixed_orbit_of_pow {p : ℕ} [Fact p.Prime]
    (P : Parameters) (hp : P.prime = 2) (σ : CoefficientAut P) (hσ : σ ^ p = 1)
    (a : OrbitParameters P) (ha : a ^ p = 1) :
    coefficientCarrier P σ (toCarrier P (orbitElementary P hp a)) =
      toCarrier P (orbitElementary P hp a) := by
  have ha1 : a.1 ^ p = 1 := congrArg Prod.fst ha
  have ha2 : a.2 ^ p = 1 := congrArg Prod.snd ha
  have hunit (i : Fin 4) : Units.map σ.toMonoidHom (expand P a i) = expand P a i := by
    apply coefficient_fixes_unit P σ hσ
    fin_cases i <;> simp [expand, ← map_pow, ha1, ha2]
  have he : coefficientSplit P σ (elementaryInclusion P (orbitElementary P hp a)) =
      elementaryInclusion P (orbitElementary P hp a) := by
    simp only [inclusion_orbitElementary, product, map_mul, coefficient_word, hunit]
  exact fixed_image_of_split_fixed P σ (orbitElementary P hp a) he

/-- The two split-torus coordinates give a p² subgroup fixed by the actual coefficient actor. -/
theorem exists_fixed_elementary (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ 2 ^ n - 1)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p) :
    ∃ E : Subgroup (BinaryCarrier n hn), IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (coefficientAction (binaryParameters n hn) σ).fixedSubgroup := by
  let P := binaryParameters n hn
  obtain ⟨B, hB, hcB⟩ := ReeSplit.elementary_pair
    (show p ∣ Nat.card (fixedField P) - 1 by rwa [card_fixedField])
  let := hB
  let j : (fixedField P)ˣ × (fixedField P)ˣ →* OrbitParameters P :=
    (fixedUnit P).prodMap (MonoidHom.id _)
  have hj : Function.Injective j := by
    intro x y h
    apply Prod.ext
    · apply Units.ext
      apply Subtype.ext
      exact congrArg Units.val (congrArg Prod.fst h)
    · exact congrArg (fun z : OrbitParameters P => z.2) h
  let f : (fixedField P)ˣ × (fixedField P)ˣ →* Carrier P :=
    (torus P).subtype.comp ((torusMulEquiv P rfl).toMonoidHom.comp j)
  have hf : Function.Injective f :=
    (torus P).subtype_injective.comp ((torusMulEquiv P rfl).injective.comp hj)
  refine ⟨B.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [card_map_of_injective hf, hcB]
  · rintro _ ⟨x, hx, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hxp : x ^ p = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p B) (⟨x, hx⟩ : B))
    change coefficientCarrier P σ (toCarrier P (orbitElementary P rfl (j x))) = _
    apply fixed_orbit_of_pow P rfl σ (hσ ▸ pow_orderOf_eq_one σ)
    rw [← map_pow, hxp, map_one]

end TrialitySplit
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
namespace TrialitySplit
open Triality.Standard Triality.Standard.OuterOdd

/-- The fixed split torus and a noninner coefficient actor give an elementary
subgroup of rank three in the literal automorphism overgroup. -/
theorem field_actor_rank_three (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ 2 ^ n - 1)
    (A : Subgroup (MulAut (BinaryCarrier n hn)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ A)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p)
    (hb : orderOf (coefficientAction _ σ) = p)
    (hbA : coefficientAction _ σ ∈ A)
    (hout : coefficientAction _ σ ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_elementary n hn hd σ hσ
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

/-- Every prime actor at a split-torus prime is inner in a rank-two
full-inner automorphism overgroup of the genuine triality model. -/
theorem prime_actor_inner (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ 2 ^ n - 1)
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

end TrialitySplit

variable {H : Type*} [Group H] [Finite H]

/-- Exclude the ordinary triality row at a split-torus prime using the
actual outside actor and inherited SQTK rank bound. -/
theorem ordinary_not_triality_split_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] [IsQuasisimple K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < primeRank p K) (hz : Nat.Coprime p (Nat.card (center K)))
    {n : ℕ} (hn : 1 ≤ n) (hd : p ∣ 2 ^ n - 1)
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
  apply TrialitySplit.prime_actor_inner n hn0 hd f.range
    (by rw [← normalAction_component_image K e]; exact Subgroup.map_le_range f K)
    (normalAction_rank_le_two hz hr hb e) (f a) ⟨a, rfl⟩
  rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]

/-- Transport the triality split-prime exclusion to the literal two-core
component, preserving the actual quotient image of the outside actor. -/
theorem not_triality_split_twoCore_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 1 ≤ n) (hd : p ∣ 2 ^ n - 1)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 1 < primeRank p (twoCoreComponent K) := by rwa [twoCore_rank hK ho]
  have ha' := twoCore_actor hp ho a ha haK
  exact ordinary_not_triality_split_model (twoCore_sqtk hH) hp ho hr' hz' hn hd
    (hmodel.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK)))
    (QuotientGroup.mk' (pCore 2 H) a) ha'.1 ha'.2

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The exceptional field rows at primes outside the split torus. -/
def ExceptionalNonsplitModel (p : ℕ) (S : Type*) [Group S] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ ¬ p ∣ 2 ^ n - 1 ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ¬ p ∣ 2 ^ (2 * m + 1) - 1 ∧ IsReeF4At S m)

variable {H : Type*} [Group H] [Finite H]

/-- The remaining exceptional primes avoid the split torus; the actual
outer action on a central cubic cover is retained without modification. -/
def NonsplitOrCoverRemainder (p : ℕ) (K : Subgroup H) (a : H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    ExceptionalNonsplitModel p ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ OuterCubicCoverActor (twoCoreComponent K) (QuotientGroup.mk' (pCore 2 H) a))

/-- Apply both fixed split-torus exclusions on the original normal
split-prime domain. Every remaining source branch stays explicit. -/
theorem alternatives_or_nonsplit_or_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ NonsplitOrCoverRemainder p K a := by
  rcases alternatives_or_outer_cover hH hK hp ho hr a ha haK hgen with halt | hrem
  · exact Or.inl halt
  rcases hrem with ⟨hp3, hz, hm⟩ | hcover
  · apply Or.inr
    apply Or.inl
    refine ⟨hp3, hz, ?_⟩
    rcases hm with ⟨n, hn, hm⟩ | ⟨m, hm, he⟩
    · exact Or.inl ⟨n, hn, fun hd =>
        not_triality_split_twoCore_model hH hK hp ho hr hz hn hd hm a ha haK, hm⟩
    · exact Or.inr ⟨m, hm, fun hd =>
        not_ree_split_twoCore_model hH hK hp ho hr hz hm hd he a ha haK, he⟩
  · exact Or.inr (Or.inr hcover)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
