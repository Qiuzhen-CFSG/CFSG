module
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Theory.GroupAction.SixteenOddComplements.ThirtySix
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Splitting above the normal nine on binary sixteen

A self-centralizing normal elementary sixteen has a complement whenever its
quotient has order36 and trivial two-core. The quotient's three-core has
order9. Its preimage is the product of the sixteen and a Sylow three-subgroup.
The latter has trivial fixed group on the sixteen: coprime splitting and the
binary automorphism orders in dimensions below four rule out a fixed summand.
Frattini then makes its normalizer the required complement.

This retains the actual normalizer complement used to recognize N(A₂) in
Aschbacher--Smith F.5.7, printed p.303.
-/
open Subgroup
open scoped IsMulCommutative
namespace SixteenOddComplements
private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

public theorem fixed_eq_bot_of_nine
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



variable {G : Type*} [Group G] [Finite G]
public theorem normalizer_complement_of_nine
    (A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hC : centralizer (A : Set G) ≤ A)
    (P : Sylow 3 G) (hP : Nat.card P = 9) [(A ⊔ (P : Subgroup G)).Normal] :
    A.IsComplement' (normalizer ((P : Subgroup G) : Set G)) := by
  have hd : Disjoint A (P : Subgroup G) := disjoint_of_coprime_natCard (by rw [hA,hP];decide)
  let f : P →* MulAut A := MulAut.conjNormal.comp (P : Subgroup G).subtype
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro p hp
    apply Subtype.ext
    apply hd.le_bot
    refine ⟨hC ?_,p.property⟩
    intro a ha
    have he := congrArg (fun k : MulAut A => (k ⟨a,ha⟩).val) hp
    change (p : G)*a*(p : G)⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hF : Nat.card f.range = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).symm.trans hP
  have hfixed := fixed_eq_bot_of_nine hA f.range hF
  have hcent : A ⊓ centralizer ((P : Subgroup G) : Set G) = ⊥ := by
    apply bot_unique
    intro a ha
    have hmem : (⟨a,ha.1⟩ : A) ∈ FixedPoints.subgroup f.range A := by
      rintro ⟨u,p,rfl⟩
      apply Subtype.ext
      change (p:G)*a*(p:G)⁻¹=a
      rw [ha.2 p p.property,mul_inv_cancel_right]
    exact congrArg Subtype.val (hfixed.le hmem)
  have hdis : Disjoint A (normalizer ((P : Subgroup G) : Set G)) := by
    rw [disjoint_iff,SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf A P
      (by rw [A.normalizer_eq_top];exact le_top) hd,hcent]
  have hsup : A ⊔ normalizer ((P : Subgroup G) : Set G) = ⊤ := by
    have hh := P.normalizer_sup_eq_top' (show (P : Subgroup G) ≤ A ⊔ P from le_sup_right)
    change normalizer ((P : Subgroup G) : Set G) ⊔ (A ⊔ (P : Subgroup G)) = ⊤ at hh
    rwa [sup_left_comm,sup_eq_left.mpr (P : Subgroup G).le_normalizer] at hh
  apply isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← coe_mul_of_right_le_normalizer_left _ _ (by rw [A.normalizer_eq_top];exact le_top),hsup]
  rfl

public theorem exists_complement_of_quotient_thirty_six
    (A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hC : centralizer (A : Set G) ≤ A)
    (hQ : Nat.card (G ⧸ A) = 36) (hcore : pCore 2 (G ⧸ A) = ⊥) :
    ∃ B : Subgroup G, A.IsComplement' B := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := default
  have hG : Nat.card G = 576 := by
    rw [card_eq_card_quotient_mul_card_subgroup A,hQ,hA]
  have hP : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity,hG]
    decide +kernel
  let q := QuotientGroup.mk' A
  let S := P.mapSurjective (f:=q) (QuotientGroup.mk'_surjective A)
  have hS : Nat.card S = 9 := by
    rw [S.card_eq_multiplicity,hQ]
    decide +kernel
  have hJ := threeCore_card_of_reduced_thirty_six hQ hcore
  have he : pCore 3 (G ⧸ A) = (S : Subgroup (G ⧸ A)) :=
    eq_of_le_of_card_ge (pCore_isPGroup.le_sylow_of_normal S) (by rw [hS,hJ])
  have hpre : (pCore 3 (G ⧸ A)).comap q = A ⊔ (P : Subgroup G) := by
    rw [he]
    change ((P : Subgroup G).map q).comap q = _
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_comm]
  let : (A ⊔ (P : Subgroup G)).Normal := hpre ▸ inferInstance
  exact ⟨normalizer ((P : Subgroup G) : Set G),normalizer_complement_of_nine A hA hC P hP⟩
end SixteenOddComplements
