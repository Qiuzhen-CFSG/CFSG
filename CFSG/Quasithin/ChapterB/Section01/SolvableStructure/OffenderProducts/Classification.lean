module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.LinearAlgebra.IntersectionCodimension

/-!
# Classification of best offenders in the internal natural factors

Given the concrete internal factors of B.1.8(1)–(2) and the ratio-one
conclusion of (3), we prove the equivalence in (4). The right-hand side uses
the inclusion-images of actual Sylow subgroups from `Choices`.

For the forward implication, project an elementary abelian offender onto
each factor. Each image is trivial or Sylow of order two. Its nontrivial
coordinates each cost at least one fixed codimension: fixed vectors in the
sum of the supports inject into the product of the coordinate fixed spaces.
The offender inequality then forces the subgroup to fill its coordinate
product, by comparison of orders.

For the reverse implication, an involution's displacement lies in its
two-dimensional support and is fixed by that involution. The natural action
is faithful on the support, so the displacement has dimension at most one.
Codimension is subadditive for intersections of fixed spaces. Thus each
nontrivial Sylow product is an offender, and ratio one, via Thompson
replacement, makes it a best offender.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.8(4), printed p. 70 (PDF p. 81), combined manuscript of 1 March 2004.
-/

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

private noncomputable def factorProjection (i : Fin d.count) : offenderSubgroup ρ →* d.factor i :=
  (Pi.evalMonoidHom (fun j => d.factor j) i).comp d.groupProduct.symm.toMonoidHom

private noncomputable def supportRepresentation (i : Fin d.count) :
    Representation (ZMod 2) (offenderSubgroup ρ) (subspaceCommutator ρ ⊤ (d.factor i)) :=
  (stabilizerRepresentation ρ _).comp
    (Subgroup.inclusion (d.offenderSubgroup_le_support_stabilizer i))

private theorem product_action_support (x : (i : Fin d.count) → d.factor i)
    (i : Fin d.count) (v : subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ (d.productInclusion x) (v : V) = ρ (x i : G) (v : V) := by
  let τ := d.supportRepresentation i
  have he : τ.comp d.groupProduct.toMonoidHom =
      (τ.comp (Subgroup.inclusion (d.factor_le_offenderSubgroup i))).comp
        (Pi.evalMonoidHom (fun j => d.factor j) i) := by
    apply MonoidHom.pi_ext
    intro j g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ρ (d.groupProduct (Pi.mulSingle j g) : G) (w : V) =
      ρ ((Pi.mulSingle (M := fun k => d.factor k) j g i : d.factor i) : G) (w : V)
    rw [d.groupProduct_single]
    by_cases hji : j = i
    · subst j
      simp
    · simp only [Pi.mulSingle_eq_of_ne (Ne.symm hji), OneMemClass.coe_one, map_one,
        Module.End.one_apply]
      exact d.factor_fixes_other_support hji g w.property
  exact congrArg (fun f => (f v : V)) (DFunLike.congr_fun he x)

private theorem projection_action_support (g : offenderSubgroup ρ)
    (i : Fin d.count) (v : subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ (g : G) (v : V) = ρ (d.factorProjection i g : G) (v : V) := by
  change ρ (g : G) (v : V) = ρ (d.groupProduct.symm g i : G) (v : V)
  have := d.product_action_support (d.groupProduct.symm g) i v
  simpa only [productInclusion, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.subtype_apply, MulEquiv.apply_symm_apply] using this

private theorem factor_support_faithful (i : Fin d.count) (g : d.factor i)
    (h : ∀ v : subspaceCommutator ρ ⊤ (d.factor i), ρ (g : G) (v : V) = v) : g = 1 := by
  apply (d.factorModel i).injective
  rw [map_one]
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_one]
  apply LinearEquiv.ext
  intro w
  have hv := h ((d.naturalEquiv i).symm w)
  rw [d.naturalEquiv_action] at hv
  have hh := congrArg (d.naturalEquiv i) (Subtype.val_injective hv)
  change Representation.specialLinearNatural 2 (d.factorModel i g) w = w
  simpa only [LinearEquiv.apply_symm_apply] using hh

private noncomputable def coordinateHom (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ)
    (i : Fin d.count) : A →* d.factor i :=
  (d.factorProjection i).comp (Subgroup.inclusion hA)

private noncomputable def coordinateChoice (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ)
    (i : Fin d.count) : Subgroup G :=
  (d.coordinateHom A hA i).range.map (d.factor i).subtype

private theorem coordinateChoice_le (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ)
    (i : Fin d.count) : d.coordinateChoice A hA i ≤ d.factor i := by
  rintro g ⟨x, _, rfl⟩
  exact x.property

private theorem coordinateChoice_isSylowChoice [Finite G] (A : Subgroup G)
    (hA : A ≤ offenderSubgroup ρ) (he : IsElementaryAbelian 2 A) (i : Fin d.count) :
    d.IsSylowChoice i (d.coordinateChoice A hA i) := by
  let := he
  let R := (d.coordinateHom A hA i).range
  have hp : IsPGroup 2 R := (IsElementaryAbelian.isPGroup 2 A).of_surjective
    (d.coordinateHom A hA i).rangeRestrict (d.coordinateHom A hA i).rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  by_cases hR : R = ⊥
  · left
    change R.map _ = ⊥
    simp [hR]
  · right
    refine ⟨S, ?_⟩
    have heq : R = (S : Subgroup (d.factor i)) := by
      apply Subgroup.eq_of_le_of_card_ge hS
      have hc := d.factorSylow_card i S
      rw [factorSylow, Subgroup.card_map_of_injective Subtype.val_injective] at hc
      have hn := Nat.card_pos (α := R)
      have hne : Nat.card R ≠ 1 := fun h => hR (Subgroup.card_eq_one.mp h)
      change Nat.card S ≤ Nat.card R
      omega
    change R.map _ = _
    rw [heq]
    rfl

private theorem le_iSup_coordinateChoice (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ) :
    A ≤ ⨆ i, d.coordinateChoice A hA i := by
  intro a ha
  let x : (i : Fin d.count) → d.coordinateChoice A hA i := fun i =>
    ⟨d.coordinateHom A hA i ⟨a, ha⟩, ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩⟩
  have hx : d.subproductInclusion (d.coordinateChoice A hA)
      (d.coordinateChoice_le A hA) x = a := by
    change (d.groupProduct (d.groupProduct.symm ⟨a, hA ha⟩) : G) = a
    rw [MulEquiv.apply_symm_apply]
  rw [← d.subproductInclusion_range (d.coordinateChoice A hA) (d.coordinateChoice_le A hA)]
  exact ⟨x, hx⟩

private noncomputable def fixedSupport (A : Subgroup G) (i : Fin d.count) :
    Submodule (ZMod 2) (subspaceCommutator ρ ⊤ (d.factor i)) :=
  (fixedSpace ρ A).comap (subspaceCommutator ρ ⊤ (d.factor i)).subtype

private theorem sumInclusion_action (g : offenderSubgroup ρ)
    (x : (i : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ (g : G) (d.sumInclusion x) =
      d.sumInclusion (fun i => d.supportRepresentation i g (x i)) := by
  calc
    _ = ∑ i, ρ (g : G) (x i : V) := by
      conv_lhs => rw [← Finset.univ_sum_single x, map_sum, map_sum]
      simp only [d.sumInclusion_single]
    _ = _ := by
      rw [← Finset.univ_sum_single (fun i => d.supportRepresentation i g (x i)), map_sum]
      simp only [d.sumInclusion_single]
      rfl

private theorem fixed_sum_coordinate (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ)
    (x : (i : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor i))
    (hx : d.sumInclusion x ∈ fixedSpace ρ A) (i : Fin d.count) :
    x i ∈ d.fixedSupport A i := by
  intro a
  have he := (d.sumInclusion_action ⟨a, hA a.property⟩ x).symm.trans (hx a)
  exact congrArg Subtype.val (congrFun (d.sumInclusion_injective he) i)

private noncomputable def fixedSumCoordinates (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ) :
    (subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ⊓ fixedSpace ρ A : Submodule (ZMod 2) V)
      →ₗ[ZMod 2] ((i : Fin d.count) → d.fixedSupport A i) where
  toFun v i := ⟨d.moduleSum.symm ⟨v, v.property.1⟩ i,
    d.fixed_sum_coordinate A hA _ (by
      change (d.moduleSum (d.moduleSum.symm ⟨v, v.property.1⟩) : V) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact v.property.2) i⟩
  map_add' v w := by ext i; exact congrArg (fun x => (x i : V)) (map_add d.moduleSum.symm ⟨v, v.property.1⟩ ⟨w, w.property.1⟩)
  map_smul' c v := by ext i; exact congrArg (fun x => (x i : V)) (map_smul d.moduleSum.symm c ⟨v, v.property.1⟩)

private theorem fixedSumCoordinates_injective (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ) :
    Function.Injective (d.fixedSumCoordinates A hA) := by
  intro v w he
  apply Subtype.ext
  have hh : d.moduleSum.symm ⟨v, v.property.1⟩ = d.moduleSum.symm ⟨w, w.property.1⟩ := by
    funext i
    exact congrArg Subtype.val (congrFun he i)
  exact congrArg (fun z : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) => (z : V))
    (d.moduleSum.symm.injective hh)

private theorem coordinateChoice_eq_bot_of_fixedSupport_eq_top (A : Subgroup G)
    (hA : A ≤ offenderSubgroup ρ) (i : Fin d.count) (hfix : d.fixedSupport A i = ⊤) :
    d.coordinateChoice A hA i = ⊥ := by
  apply bot_unique
  rintro x ⟨g, ⟨a, rfl⟩, rfl⟩
  apply Subgroup.mem_bot.mpr
  have he : d.coordinateHom A hA i a = 1 := by
    apply d.factor_support_faithful i
    intro v
    have hv : v ∈ d.fixedSupport A i := hfix ▸ Submodule.mem_top
    exact (d.projection_action_support ⟨a, hA a.property⟩ i v).symm.trans (hv a)
  exact congrArg Subtype.val he

private theorem sylowChoice_card (i : Fin d.count) (C : Subgroup G)
    (hC : d.IsSylowChoice i C) : Nat.card C = 2 ^ rank C := by
  rcases hC with rfl | ⟨S, rfl⟩
  · simp
  · rw [rank, d.factorSylow_card]
    decide

private theorem sylowChoice_rank_le_one (i : Fin d.count) (C : Subgroup G)
    (hC : d.IsSylowChoice i C) : rank C ≤ 1 := by
  rcases hC with rfl | ⟨S, rfl⟩
  · simp
  · rw [rank, d.factorSylow_card]
    decide

private theorem sylowProduct_card (C : Fin d.count → Subgroup G)
    (hC : ∀ i, d.IsSylowChoice i (C i)) :
    Nat.card (⨆ i, C i : Subgroup G) = 2 ^ (∑ i, rank (C i)) := by
  rw [d.subproduct_card C (fun i => IsSylowChoice.le d (hC i))]
  simp_rw [d.sylowChoice_card _ _ (hC _)]
  rw [Finset.prod_pow_eq_pow_sum]

private theorem coordinate_rank_le_fixedCodim [Finite G] [FiniteDimensional (ZMod 2) V]
    (A : Subgroup G) (hA : A ≤ offenderSubgroup ρ) (he : IsElementaryAbelian 2 A) :
    (∑ i, rank (d.coordinateChoice A hA i)) ≤ fixedCodim ρ A := by
  have hbound (i : Fin d.count) :
      rank (d.coordinateChoice A hA i) + Module.finrank (ZMod 2) (d.fixedSupport A i) ≤ 2 := by
    have hr := d.sylowChoice_rank_le_one i _ (d.coordinateChoice_isSylowChoice A hA he i)
    by_cases hC : d.coordinateChoice A hA i = ⊥
    · rw [hC, Representation.BinaryOffender.rank_bot, zero_add]
      exact (Submodule.finrank_le _).trans_eq (d.support_finrank i)
    · have hn : d.fixedSupport A i ≠ ⊤ := fun h => hC
        (d.coordinateChoice_eq_bot_of_fixedSupport_eq_top A hA i h)
      have hlt := Submodule.finrank_lt hn
      rw [d.support_finrank] at hlt
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hdim := LinearMap.finrank_le_finrank_of_injective (d.fixedSumCoordinates_injective A hA)
  rw [Module.finrank_pi_fintype] at hdim
  have hgeom := (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)).finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ A)
  have hle := Submodule.finrank_le
    (subspaceCommutator ρ ⊤ (offenderSubgroup ρ) ⊔ fixedSpace ρ A : Submodule (ZMod 2) V)
  have hnull := fixedCodim_add_finrank ρ A
  rw [d.commutator_finrank] at hgeom
  omega

private theorem isSylowProduct_of_bestOffender [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsBestOffender ρ A) : d.IsSylowProduct A := by
  classical
  have hAJ : A ≤ offenderSubgroup ρ :=
    le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl)
  let C := d.coordinateChoice A hAJ
  have hC : ∀ i, d.IsSylowChoice i (C i) := d.coordinateChoice_isSylowChoice A hAJ hA.1.2
  have hle : A ≤ ⨆ i, C i := d.le_iSup_coordinateChoice A hAJ
  have heq : A = ⨆ i, C i := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [d.sylowProduct_card C hC, hA.1.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide) ((d.coordinate_rank_le_fixedCodim A hAJ hA.1.2).trans
      (hA.isOffender ρ).2)
  refine ⟨C, hC, ?_, heq⟩
  by_contra hn
  push Not at hn
  apply hA.1.1
  rw [heq]
  simp only [hn, iSup_bot]

private theorem sylowChoice_pow_two [Finite G] (i : Fin d.count) (C : Subgroup G)
    (hC : d.IsSylowChoice i C) (a : C) : a ^ 2 = 1 := by
  rcases hC with rfl | ⟨S, rfl⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.mem_bot.mp a.property, one_pow, OneMemClass.coe_one]
  · simpa only [d.factorSylow_card i S] using (pow_card_eq_one' (x := a))

private theorem IsSylowProduct.isElementaryTwo [Finite G] {A : Subgroup G}
    (hA : d.IsSylowProduct A) : IsElementaryTwo A := by
  have hne := hA.ne_bot d
  obtain ⟨C, hC, _, rfl⟩ := hA
  let e := d.subproductEquiv C (fun i => IsSylowChoice.le d (hC i))
  have hpow (a : (⨆ i, C i : Subgroup G)) : a ^ 2 = 1 := by
    apply e.symm.injective
    simp only [map_pow, map_one]
    funext i
    exact d.sylowChoice_pow_two i _ (hC i) (e.symm a i)
  refine ⟨hne, { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }⟩
  · intro a b
    exact (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hpow c)) a b).eq
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow

private theorem factorSylow_fixedCodim_le_one [Finite G] [FiniteDimensional (ZMod 2) V]
    (i : Fin d.count) (S : Sylow 2 (d.factor i)) :
    fixedCodim ρ (d.factorSylow i S) ≤ 1 := by
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (d.factorSylow_ne_bot i S)
  have ht2 : (t : G) ^ 2 = 1 :=
    congrArg Subtype.val (d.sylowChoice_pow_two i _ (Or.inr ⟨S, rfl⟩) t)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  have ho : orderOf (t : G) = 2 := orderOf_eq_prime ht2 ht1
  have hcyc : Subgroup.zpowers (t : G) = d.factorSylow i S := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t.property)
    rw [Nat.card_zpowers, ho, d.factorSylow_card]
  rw [← hcyc, fixedCodim_zpowers_eq_displacement_rank]
  let R := LinearMap.range (ρ (t : G) - LinearMap.id)
  let W := subspaceCommutator ρ ⊤ (d.factor i)
  have hle : R ≤ W := by
    rintro v ⟨w, rfl⟩
    exact Submodule.subset_span ⟨t, d.factorSylow_le i S t.property, w, Submodule.mem_top, rfl⟩
  have hne : R ≠ W := by
    intro heq
    have he : (⟨t, d.factorSylow_le i S t.property⟩ : d.factor i) = 1 := by
      apply d.factor_support_faithful i
      intro v
      have hv : (v : V) ∈ R := heq.symm ▸ v.property
      obtain ⟨w, hw⟩ := hv
      rw [← hw]
      exact involution_fixes_displacement ρ (by simpa only [pow_two] using ht2) w
    exact ht1 (congrArg Subtype.val he)
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hdim : Module.finrank (ZMod 2) W = 2 := d.support_finrank i
  change Module.finrank (ZMod 2) R ≤ 1
  omega

private theorem fixedSpace_iSup {ι : Type*} (C : ι → Subgroup G) :
    fixedSpace ρ (⨆ i, C i) = ⨅ i, fixedSpace ρ (C i) := by
  ext v
  constructor
  · intro hv
    exact (Submodule.mem_iInf _).mpr fun i a => hv ⟨a, le_iSup C i a.property⟩
  · intro hv a
    refine Subgroup.iSup_induction C (C := fun a => ρ a v = v) a.property ?_ ?_ ?_
    · intro i a ha
      exact ((Submodule.mem_iInf _).mp hv i) ⟨a, ha⟩
    · simp
    · intro a b ha hb
      simp only [map_mul, Module.End.mul_apply, ha, hb]

private theorem sylowProduct_fixedCodim_le_rank [Finite G] [FiniteDimensional (ZMod 2) V]
    (C : Fin d.count → Subgroup G) (hC : ∀ i, d.IsSylowChoice i (C i)) :
    fixedCodim ρ (⨆ i, C i) ≤ rank (⨆ i, C i) := by
  have hbound (i : Fin d.count) : fixedCodim ρ (C i) ≤ rank (C i) := by
    rcases hC i with hbot | ⟨S, hS⟩
    · rw [hbot, fixedCodim, Representation.BinaryOffender.fixedSpace_bot]
      simp [Submodule.finrank_quotient]
    · rw [hS]
      have h := d.factorSylow_fixedCodim_le_one i S
      simpa only [rank, d.factorSylow_card i S, show Nat.log 2 2 = 1 from rfl] using h
  unfold fixedCodim
  rw [fixedSpace_iSup]
  have h := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (C i))
  have hr : rank (⨆ i, C i) = ∑ i, rank (C i) := by
    rw [rank, d.sylowProduct_card C hC, Nat.log_pow (by decide : 1 < 2)]
  rw [hr]
  exact h.trans (Finset.sum_le_sum fun i _ => hbound i)

private theorem isBestOffender_of_sylowProduct [Finite G] [FiniteDimensional (ZMod 2) V]
    (hq : quadraticRatio ρ = 1) {A : Subgroup G} (hA : d.IsSylowProduct A) :
    IsBestOffender ρ A := by
  have hn : ¬ IsStrongFFModule ρ := by
    intro h
    have hh := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp h
    simp [hq] at hh
  have he := hA.isElementaryTwo d
  obtain ⟨C, hC, _, rfl⟩ := hA
  apply (isBestOffender_iff_of_not_strong ρ hn _).mpr
  refine ⟨he, le_antisymm (d.sylowProduct_fixedCodim_le_rank C hC) ?_⟩
  exact Nat.le_of_not_gt (fun h => hn ⟨_, he, h⟩)

/-- B.1.8(4), conditional only on the actual internal natural factors and
quadratic ratio one: best offenders are precisely nontrivial Sylow products. -/
public theorem isBestOffender_iff_sylowProduct [Finite G] [FiniteDimensional (ZMod 2) V]
    (_hfaith : Function.Injective ρ) (hq : quadraticRatio ρ = 1) (A : Subgroup G) :
    IsBestOffender ρ A ↔ d.IsSylowProduct A := by
  exact ⟨d.isSylowProduct_of_bestOffender, d.isBestOffender_of_sylowProduct hq⟩

end CFSG.Quasithin.ChapterB.SolvableFFFactors
