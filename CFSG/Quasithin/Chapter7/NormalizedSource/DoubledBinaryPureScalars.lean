module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCartan

/-!
# Scalar actors in the original pure-line image

The literal inner-action marking transports centralization by the original core
to its lifted image in a centerless component. A scalar group acting freely on
one nonidentity inner actor then embeds in the pure-line action on the whole
orbit. That image has order dividing 24, so odd scalar groups have order at most
three. The G₂ and triality applications retain the actual component embedding.
Source: Aschbacher–Smith 7.7.3 and 7.7.4, printed pp.704–706.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureScalars

private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- The equivalence uses the literal quotient map, whose kernel is trivial. -/
@[expose] def centerlessQuotient {K : Type*} [Group K] (hz : center K = ⊥) :
    K ≃* K ⧸ center K :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center K))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hz]),
      QuotientGroup.mk'_surjective _⟩

/-- A core fixing the marked actors fixes their unique lifts into a centerless component. -/
theorem original_fixed_inner_image
    {G : Type*} [Group G] (K A Q : Subgroup G)
    (hz : center K = ⊥) (hAN : A ≤ normalizer (K : Set G))
    (hQN : Q ≤ normalizer (K : Set G)) (hQA : Q ≤ centralizer (A : Set G))
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a)) :
    Q ≤ centralizer ((j.range.map (centerlessQuotient hz).symm.toMonoidHom).map K.subtype : Set G) := by
  intro q hq
  apply mem_centralizer_iff.mpr
  rintro x ⟨k,⟨z,⟨a,rfl⟩,rfl⟩,rfl⟩
  let c := centerlessQuotient hz
  let k : K := c.symm (j a)
  let β := K.normalizerMonoidHom ⟨q,hQN hq⟩
  have hk : (QuotientGroup.mk' (center K)) k = j a := c.apply_symm_apply _
  have hconj : MulAut.conj k = K.normalizerMonoidHom (inclusion hAN a) := by
    rw [←hact a,←hk,←inner_conj k,MulEquiv.symm_apply_apply]
    rfl
  have hc : Commute β (MulAut.conj k) := by
    rw [hconj]
    apply Commute.map
    exact (Subtype.ext ((mem_centralizer_iff.mp (hQA hq) a a.property).symm) :
      (⟨q,hQN hq⟩ : normalizer (K : Set G)) * inclusion hAN a =
        inclusion hAN a * ⟨q,hQN hq⟩)
  have hf : β k = k := by
    apply conj_injective_of_center_eq_bot hz
    apply MulEquiv.ext
    intro y
    have hh := congrArg (fun f : MulAut K => f (β.symm y)) hc.eq
    change β (k * β.symm y * k⁻¹) = k * β (β.symm y) * k⁻¹ at hh
    simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply,MulAut.conj_apply] using hh
  have hh := congrArg Subtype.val hf
  change q * (k : G) * q⁻¹ = k at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Freeness on one marked inner actor makes the scalar action on the orbit faithful. -/
theorem torus_card_dvd
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (W U K A : Subgroup G) (hAW : A ≤ W) (hKC : K ≤ centralizer (U : Set G))
    (hAN : A ≤ normalizer (K : Set G))
    (he : Nat.card (ChapterE.inducedAutomizer W (centralizer (U : Set G))) ∣ 24)
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (b : X →* K) (hBW : b.range.map K.subtype ≤ normalizer (W : Set G))
    (a : A) (hfree : ∀ x : X, Commute (j a) (QuotientGroup.mk' (center K) (b x)) → x = 1) :
    Nat.card X ∣ 24 := by
  let f : X →* normalizer (W : Set G) := (K.subtype.comp b).codRestrict _
    (fun x => hBW (mem_map_of_mem K.subtype (show b x ∈ b.range from ⟨x,rfl⟩)))
  let r₀ := W.normalizerMonoidHom.rangeRestrict.comp f
  let r : X →* ChapterE.inducedAutomizer W (centralizer (U : Set G)) :=
    r₀.codRestrict _ (fun x => ⟨f x,hKC (b x).property,rfl⟩)
  have hr : r.ker = ⊥ := by
    apply bot_unique
    intro x hx
    have hxW : ((b x : K) : G) ∈ centralizer (W : Set G) := by
      have hh : W.normalizerMonoidHom (f x) = 1 :=
        congrArg (fun y : ChapterE.inducedAutomizer W (centralizer (U : Set G)) => y.val.val) hx
      change f x ∈ W.normalizerMonoidHom.ker at hh
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    apply hfree
    let e := innerEquivCentralQuotient (H := K)
    have hf : (e.symm (j a) : MulAut K) (b x) = b x := by
      rw [hact a]
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hxW a (hAW a.property))
    have hq : e.symm (QuotientGroup.mk' (center K) (b x)) =
        (MulAut.conj : K →* MulAut K).rangeRestrict (b x) := by
      apply e.injective
      rw [e.apply_symm_apply,inner_conj]
    apply e.symm.injective
    rw [map_mul,map_mul,hq]
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    change (e.symm (j a) : MulAut K) (b x * y * (b x)⁻¹) =
      b x * (e.symm (j a) : MulAut K) y * (b x)⁻¹
    rw [map_mul,map_mul,map_inv,hf]
  have hc := Nat.card_congr (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff r).mp hr)).toEquiv
  rw [hc]
  exact r.range.card_subgroup_dvd_card.trans he

/-- An odd scalar group acting faithfully in the pure-line image has order at most three. -/
theorem scalar_card_le_three {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (B : Subgroup Fˣ) (hB : Nat.card B ∣ 24) : Nat.card B ≤ 3 := by
  have ho : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units,hF,Nat.odd_iff]
    have hd : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
    have hh := Nat.mod_eq_zero_of_dvd hd
    have hp : 0 < 2^n := pow_pos (by decide) n
    omega
  have hodd : Odd (Nat.card B) := ho.of_dvd_nat B.card_subgroup_dvd_card
  have hc : (Nat.card B).Coprime 8 := by simpa using hodd.coprime_two_right.pow_right 3
  exact Nat.le_of_dvd (by decide : 0 < 3) (hc.dvd_of_dvd_mul_left hB)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureScalars
