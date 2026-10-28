module

public import Theory.GroupAction.NineSixteenFixedFactors
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The two-residual of an order-nine normalizer on elementary sixteen

For an elementary abelian two-group E of order sixteen and any subgroup A
of order nine in Aut(E), the two-residual of its full normalizer is A.
The subgroup A is elementary abelian. Coprime splitting first shows that
its common fixed subgroup is trivial: its action on the moving summand
is faithful, and no smaller binary space admits an order-nine subgroup.

The two complementary four-element fixed factors of A are preserved by
its centralizer. Restriction embeds that centralizer in GL₂(2) × GL₂(2),
so its order divides 36. Conjugation embeds the normalizer modulo the
centralizer in Aut(A) = GL₂(3), of order 48. Intersecting this order bound
with |GL₄(2)| = 20160 gives a normalizer order dividing 576 = 9 · 64.
Consequently the quotient by A is a two-group. Since A has odd order,
it is two-perfect, and the residual equality follows.

This is the automizer calculation used for both elementary-sixteen layers
in Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of
15.3.59, printed p.1150 (`refs/quasithin.pdf`, PDF p.1167). The theorem is
independent of the chapter setup and requires no additional action or
normalizer hypotheses.
-/

open Subgroup
open scoped IsMulCommutative

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem fixed_eq_bot
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    FixedPoints.subgroup A E = ⊥ := by
  let F := FixedPoints.subgroup A E
  let U := commutatorAction A E
  let : IsInvariant A E U := commutatorAction_isInvariant
  have hcompl : IsCompl F U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : E => mul_comm x y))
      (by rw [hA, hE]; decide) inferInstance
  have hcount : Nat.card F * Nat.card U = 16 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes F U
      (by rw [normalizer_eq_top]; exact le_top)
    simpa only [hcompl.inf_eq_bot, hcompl.sup_eq_top, card_bot, card_top, one_mul, hE]
      using h
  have hfaith : Function.Injective (MulDistribMulAction.toMulAut A U) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨f, hf, u, hu, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ U by rw [hcompl.sup_eq_top]; trivial)
    have hufix : a • u = u := by
      have hh := congrArg (fun b : MulAut U => b ⟨u, hu⟩) ha
      exact congrArg Subtype.val hh
    change a • (f * u) = f * u
    rw [smul_mul', hf a, hufix]
  have hdiv := Subgroup.card_dvd_of_injective (MulDistribMulAction.toMulAut A U) hfaith
  have hUdiv : Nat.card U ∣ 2 ^ 4 := by
    simpa [hE] using U.card_subgroup_dvd_card
  obtain ⟨n, hn, hU⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hUdiv
  rw [hA, SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U n hU] at hdiv
  have hUcard : Nat.card U = 16 := by
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv
    exact hU
  rw [hUcard] at hcount
  exact Subgroup.card_eq_one.mp (by change Nat.card F = 1; omega)

private theorem centralizer_card_dvd
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    Nat.card (centralizer (A : Set (MulAut E))) ∣ 36 := by
  let : IsElementaryAbelian 3 A :=
    SmallNonabelianTwoGroup.elementaryAbelian_of_card_dvd_nine
      (IsElementaryAbelian.isPGroup 2 E) (by omega) A (hA ▸ dvd_rfl)
  have hfixed : FixedPoints.subgroup (⊤ : Subgroup A) E = ⊥ := by
    apply bot_unique
    intro x hx
    apply (fixed_eq_bot hE A hA).le
    intro a
    exact hx ⟨a, mem_top a⟩
  obtain ⟨K, L, _, _, _, hK, hL, hcompl⟩ :=
    nine_sixteen_fixed_factor_decomposition hA hE hfixed
  let C := centralizer (A : Set (MulAut E))
  have hstable (J : Subgroup A) (c : C) (x : E)
      (hx : x ∈ FixedPoints.subgroup J E) : c • x ∈ FixedPoints.subgroup J E := by
    intro j
    change ((j : A) : MulAut E) • ((c : MulAut E) • x) = (c : MulAut E) • x
    have hc : ((j : A) : MulAut E) * (c : MulAut E) =
        (c : MulAut E) * ((j : A) : MulAut E) :=
      mem_centralizer_iff.mp c.property _ (j : A).property
    rw [← mul_smul, hc, mul_smul]
    exact congrArg (fun y : E => (c : MulAut E) • y) (hx j)
  let invariant (J : Subgroup A) : IsInvariant C E (FixedPoints.subgroup J E) :=
    ⟨fun c x => ⟨hstable J c x, fun h => by
      simpa only [inv_smul_smul] using hstable J c⁻¹ (c • x) h⟩⟩
  let U := FixedPoints.subgroup K E
  let W := FixedPoints.subgroup L E
  let : IsInvariant C E U := invariant K
  let : IsInvariant C E W := invariant L
  let f : C →* MulAut U × MulAut W :=
    (MulDistribMulAction.toMulAut C U).prod (MulDistribMulAction.toMulAut C W)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hc
    have hU (u : U) : (c : MulAut E) (u : E) = u :=
      congrArg Subtype.val (MulEquiv.congr_fun (congrArg Prod.fst hc) u)
    have hW (w : W) : (c : MulAut E) (w : E) = w :=
      congrArg Subtype.val (MulEquiv.congr_fun (congrArg Prod.snd hc) w)
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ U ⊔ W by rw [hcompl.sup_eq_top]; trivial)
    change (c : MulAut E) (u * w) = u * w
    rw [map_mul, hU ⟨u, hu⟩, hW ⟨w, hw⟩]
  have hdiv := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod,
    SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U 2 hK,
    SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow W 2 hL] at hdiv
  simpa [Fin.prod_univ_succ] using hdiv

private theorem card_aut_nine
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) : Nat.card (MulAut A) = 48 := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive A) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive A)
    change Nat.card A = _ at hsize
    simpa [Nat.card_zmod, hA] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive A) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let autLinear : MulAut A ≃* (Additive A ≃ₗ[ZMod 3] Additive A) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 3) (Additive A) hdim
  let coordinates := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive A)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr coordinates.toEquiv, Matrix.card_GL_field]
  norm_num [ZMod.card, Fin.prod_univ_succ]

private theorem normalizer_card_dvd
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    Nat.card (normalizer (A : Set (MulAut E))) ∣ 576 := by
  let : IsElementaryAbelian 3 A :=
    SmallNonabelianTwoGroup.elementaryAbelian_of_card_dvd_nine
      (IsElementaryAbelian.isPGroup 2 E) (by omega) A (hA ▸ dvd_rfl)
  let f := A.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 48 :=
    (card_aut_nine hA) ▸ f.range.card_subgroup_dvd_card
  have hker : Nat.card f.ker ∣ 36 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (MulAut E)))).toEquiv]
    exact centralizer_card_dvd hE A hA
  have hdiv : Nat.card (normalizer (A : Set (MulAut E))) ∣ 36 * 48 := by
    rw [← f.ker.card_mul_index, index_ker]
    exact Nat.mul_dvd_mul hker hrange
  have hGL := SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 4 hE
  norm_num [Fin.prod_univ_succ] at hGL
  have hdivGL : Nat.card (normalizer (A : Set (MulAut E))) ∣ 20160 :=
    hGL ▸ (normalizer (A : Set (MulAut E))).card_subgroup_dvd_card
  exact (show Nat.gcd (36 * 48) 20160 = 576 by decide) ▸ Nat.dvd_gcd hdiv hdivGL

/-- The two-residual of the full normalizer of an order-nine subgroup of
Aut(E), for elementary abelian E of order sixteen, maps onto that subgroup. -/
public theorem Subgroup.normalizer_residual_of_elementary_sixteen_nine
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    (pResidual 2 (normalizer (A : Set (MulAut E)))).map
      (normalizer (A : Set (MulAut E))).subtype = A := by
  let N := normalizer (A : Set (MulAut E))
  let B := A.subgroupOf N
  have hB : Nat.card B = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv).trans hA
  have hquot : IsPGroup 2 (N ⧸ B) := by
    apply IsPGroup.of_card_dvd_pow (n := 6)
    have hdiv := normalizer_card_dvd hE A hA
    have hcount := B.card_mul_index
    rw [hB] at hcount
    rw [← hcount] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 9)).mp hdiv
  have hperfect : IsPPerfect 2 B := by
    apply (pResidual_eq_top_iff 2 B).mp
    apply top_unique
    intro b _
    apply mem_pResidual_of_orderOf_coprime
    exact (show Nat.Coprime 2 9 by decide).of_dvd_right (hB ▸ _root_.orderOf_dvd_natCard b)
  rw [pResidual_eq_of_isPPerfect B hperfect hquot]
  exact map_subgroupOf_eq_of_le A.le_normalizer
