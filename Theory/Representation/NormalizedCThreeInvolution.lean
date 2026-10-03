module
public import Theory.Representation.NormalizedCThreeKernel

/-!
# Rank-two involutions normalizing a fixed-point-free C₃ action

Let an involution normalize an order-three subgroup F on an elementary
abelian two-group V. If U=[V,F] has order sixteen and the involution acts
nontrivially on U, its fixed subgroup and commutator subgroup both have
order four.

The normalizer either centralizes or inverts a generator of F. In the
inverting case the cyclotomic operator theorem supplies the four fixed
vectors. In the centralizing case, involution rank-nullity bounds the fixed
subgroup below by four, while nontriviality excludes sixteen. Its F-action
is fixed-point-free by coprime decomposition, so the fixed-point congruence
modulo three excludes order eight. Rank-nullity then gives commutator order
four in both cases.

This is the finite action assertion used in Stellmacher (1.6), journal
p. 18; see `refs/latex/stellmacher-n-group.tex`. No minimal action ratio
or prescribed order of the ambient action image is required.
-/

open scoped IsMulCommutative

namespace Representation

universe u

private theorem elementaryAbelian_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
    (IsMulCommutative.is_comm.comm (x : V) (y : V))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

public theorem normalizedCThree_involution_fixed_commutator_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (x : G) (hFcard : Nat.card F = 3)
    (hx : IsInvolution x) (hxnorm : x ∈ Subgroup.normalizer (F : Set G))
    [IsInvariant (Subgroup.zpowers x) V (commutatorAction F V)]
    (hUcard : Nat.card (commutatorAction F V) = 16)
    (hne : ∃ v ∈ commutatorAction F V, x • v ≠ v) :
    Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) (commutatorAction F V)) = 4 ∧
      Nat.card (commutatorAction (Subgroup.zpowers x) (commutatorAction F V)) = 4 := by
  let U := commutatorAction F V
  change Nat.card U = 16 at hUcard
  let R := Subgroup.zpowers x
  let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let _ : IsInvariant F V U := commutatorAction_isInvariant
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; decide)
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  have hrx : IsInvolution rx := by
    exact ⟨fun h => hx.1 (congrArg Subtype.val h), Subtype.ext hx.2⟩
  have hRcard : Nat.card R = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx.2 hx.1
  obtain ⟨hprod, hle⟩ := involution_fixed_commutator_card_data (U := U) rx hrx hRcard
  let C := FixedPoints.subgroup R U
  have hCbound : 4 ≤ Nat.card C := by
    have hcle := Subgroup.card_le_of_le hle
    change Nat.card U = Nat.card C * Nat.card (commutatorAction R U) at hprod
    rw [hUcard] at hprod
    change Nat.card (commutatorAction R U) ≤ Nat.card C at hcle
    nlinarith
  have hCnot16 : Nat.card C ≠ 16 := by
    intro h
    have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (h.trans hUcard.symm)
    obtain ⟨v, hv, hxv⟩ := hne
    have hvC : (⟨v, hv⟩ : U) ∈ C := by rw [hCtop]; trivial
    exact hxv (congrArg Subtype.val (hvC rx))
  let _ : IsCyclic F := isCyclic_of_prime_card hFcard
  obtain ⟨f, hfgen⟩ := IsCyclic.exists_generator (α := F)
  have hforder : orderOf f = 3 :=
    (orderOf_eq_card_of_forall_mem_zpowers hfgen).trans hFcard
  have hfne : f ≠ 1 := by intro h; rw [h, orderOf_one] at hforder; omega
  have hfGne : (f : G) ≠ 1 := fun h => hfne (Subtype.ext h)
  have hf3 : f ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hforder])
  have hCcard : Nat.card C = 4 := by
    rcases Subgroup.cyclicThree_normalizer_conjugates F hFcard f f.property hfGne x hxnorm with
      hcentral | hinvert
    · have hxf : Commute x (f : G) := by
        change x * (f : G) = (f : G) * x
        have h := congrArg (fun z : G => z * x) hcentral
        simpa [mul_assoc] using h
      have hgr (g : F) (r : R) : (g : G) * (r : G) = (r : G) * (g : G) := by
        obtain ⟨m, hm⟩ := hfgen g
        obtain ⟨n, hn⟩ := r.property
        change f ^ m = g at hm
        change x ^ n = (r : G) at hn
        rw [← hm, ← hn, Subgroup.coe_zpow]
        exact ((hxf.zpow_left n).zpow_right m).symm.eq
      have hsmul (g : F) (r : R) (v : U) : g • (r • v) = r • (g • v) := by
        apply Subtype.ext
        change (g : G) • ((r : G) • (v : V)) = (r : G) • ((g : G) • (v : V))
        rw [← mul_smul, ← mul_smul, hgr]
      have hforward (g : F) (v : U) (hv : v ∈ C) : g • v ∈ C := by
        intro r
        rw [← hsmul, hv r]
      let _ : IsInvariant F U C := ⟨by
        intro g v
        constructor
        · exact hforward g v
        · intro hgv
          have h := hforward g⁻¹ (g • v) hgv
          simpa only [inv_smul_smul] using h⟩
      have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
        obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
        rw [hFcard, hn]
        exact (by decide : Nat.Coprime 3 2).pow_right n
      have hcompl : IsCompl (FixedPoints.subgroup F V) U :=
        isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
          (G := V) (A := F) (Group.isSolvable_of_comm fun y z =>
            (IsMulCommutative.is_comm (M := V)).comm y z) hcop inferInstance
      have hfixFU : FixedPoints.subgroup F U = ⊥ := by
        apply Subgroup.map_injective U.subtype_injective
        rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
        simpa only [inf_comm] using hcompl.inf_eq_bot
      have hfixFC : FixedPoints.subgroup F C = ⊥ := by
        apply le_antisymm
        · intro c hc
          have hcu : (c : U) ∈ FixedPoints.subgroup F U := by
            intro g
            exact congrArg Subtype.val (hc g)
          have hc1 : (c : U) = 1 := hfixFU.le hcu
          exact Subtype.ext hc1
        · exact bot_le
      have hF3 : IsPGroup 3 F := IsPGroup.of_card (p := 3) (n := 1) (by simpa using hFcard)
      let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
      have hmod := hF3.card_modEq_card_fixedPoints C
      have hfixedCard : Nat.card (MulAction.fixedPoints F C) = 1 := by
        change Nat.card (FixedPoints.subgroup F C) = 1
        rw [hfixFC]
        simp
      rw [hfixedCard] at hmod
      have hdiv : Nat.card C ∣ 2 ^ 4 := by
        simpa [hUcard] using Subgroup.card_subgroup_dvd_card C
      obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      interval_cases k
      · change Nat.card C = 1 at hck
        omega
      · change Nat.card C = 2 at hck
        omega
      · exact hck
      · change Nat.card C = 8 at hck
        rw [hck] at hmod
        norm_num [Nat.ModEq] at hmod
      · exact (hCnot16 hck).elim
    · let ρF := Representation.ofElementaryAbelianAction (A := F) (G := U) (p := 2)
      let ρR := Representation.ofElementaryAbelianAction (A := R) (G := U) (p := 2)
      let t : Module.End (ZMod 2) (Additive U) := ρF f
      let b : Module.End (ZMod 2) (Additive U) := ρR rx
      have ht : t ^ 2 + t + 1 = 0 :=
        cardThree_commutatorAction_generator_quadratic F hFcard f hfgen hf3
      have hb : b * b = 1 := by
        change ρR rx * ρR rx = 1
        rw [← map_mul, show rx * rx = 1 by simpa only [pow_two] using hrx.2, map_one]
      have hfG2 : (f : G) ^ 2 = (f : G)⁻¹ := by
        have h := congrArg (fun z : G => z * (f : G)⁻¹) (congrArg Subtype.val hf3)
        simpa [pow_succ, mul_assoc] using h
      have hxf : x * (f : G) = (f : G) ^ 2 * x := by
        rw [hfG2]
        have h := congrArg (fun z : G => z * x) hinvert
        simpa [mul_assoc] using h
      have hbt : b * t = t ^ 2 * b := by
        apply LinearMap.ext
        intro v
        apply Additive.toMul.injective
        apply Subtype.ext
        change x • ((f : G) • ((Additive.toMul v : U) : V)) =
          (f : G) • ((f : G) • (x • ((Additive.toMul v : U) : V)))
        rw [← mul_smul, ← mul_smul, ← mul_smul, ← pow_two, hxf]
      have hcardX : Nat.card (Additive U) = 16 :=
        (Nat.card_congr Additive.toMul).trans hUcard
      have hkerCard := invertedThree_cardSixteen_fixed_card_four t b ht hb hbt hcardX
      let e : C ≃ LinearMap.ker (b - 1) :=
        { toFun := fun c => ⟨Additive.ofMul c.val, by
            change b (Additive.ofMul c.val) - Additive.ofMul c.val = 0
            exact sub_eq_zero.mpr (congrArg Additive.ofMul (c.property rx))⟩
          invFun := fun v => ⟨Additive.toMul v.val, by
            intro r
            have hxv : rx • Additive.toMul v.val = Additive.toMul v.val := by
              exact Additive.ofMul.injective (sub_eq_zero.mp v.property)
            by_cases hr : r = 1
            · simp [hr]
            · obtain ⟨z, _hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hRcard
              have hre : r = rx := (huniq r hr).trans (huniq rx hrx.1).symm
              simpa only [hre] using hxv⟩
          left_inv := by intro c; rfl
          right_inv := by intro v; rfl }
      exact (Nat.card_congr e).trans hkerCard
  refine ⟨hCcard, ?_⟩
  change Nat.card U = Nat.card C * Nat.card (commutatorAction R U) at hprod
  rw [hUcard, hCcard] at hprod
  change Nat.card (commutatorAction R U) = 4
  omega

end Representation
