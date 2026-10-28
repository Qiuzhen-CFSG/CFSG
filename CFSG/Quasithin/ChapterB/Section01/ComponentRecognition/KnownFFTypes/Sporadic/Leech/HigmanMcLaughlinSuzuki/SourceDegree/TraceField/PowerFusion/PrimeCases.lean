module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.CarrierComparison
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# The prime-seven and prime-eleven HS power-fusion cases

The ATLAS word `abababb` has order seven and a checked carrier conjugator
raises it to its square. The existing certified point-stabilizer word of order
eleven has a normalizer acting as its ninth power; applying this twice yields
the fourth power. The exact carrier order contains only one factor of each
prime, so Sylow conjugacy transfers both relations to every such element.

The same argument transfers the fixed-point counts: two at seven and one at
eleven. Commuting seven- and eleven-elements are impossible, since the latter
must fix the former's two fixed points. This excludes order 77, closing the
odd-order branch prime to fifteen in the parent `PowerFusion` module.

Every conjugator belongs to the literal ATLAS degree-100 carrier. The eleven
transport uses `SmallIndex.pointStabilizerEquivCertified`, preserving the
underlying permutation. Finite word and support checks use kernel reduction.
Source: ATLAS HSG1-p100B0 and https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
The original discovery script and conventions are retained in `source/`.
-/

public section
namespace Sporadic.LeechRelated.HS.TracePowerFusion
open OrderCertificate Theory.GroupTheory

private def a : Carrier := ⟨p0, by rw [a_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
private def b : Carrier := ⟨p1, by rw [b_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
private def seven : Carrier := a * b * a * b * a * b * b
private def letter (i : Fin 3) : Carrier := if i = 0 then a else if i = 1 then b else b⁻¹
private def conjugator : Carrier := evalWord letter
  [1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1,
  1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2,
  0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0]
private theorem seven_pow : seven ^ 7 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem seven_ne : seven ≠ 1 := by
  intro h
  have he := congrArg (fun z : Carrier => inclusion z 0) h
  exact (by decide +kernel : inclusion seven 0 ≠ 0) he
private theorem seven_order : orderOf seven = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime seven_pow seven_ne
private theorem seven_square : IsConj seven (seven ^ 2) := by
  apply isConj_iff.mpr
  refine ⟨conjugator, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- Every element of order seven in the actual HS carrier is conjugate to its square. -/
theorem orderSeven_square_fusion (g : Carrier) (hg : orderOf g = 7) : IsConj g (g ^ 2) := by
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := Carrier) (by decide : Nat.Prime 7)
    (by rw [NormalizerIndex.card_carrier]; decide) seven_order hg
  have hconj : IsConj (seven ^ k) g := isConj_iff.mpr ⟨c, hc.symm⟩
  have hpow : IsConj (seven ^ k) ((seven ^ k) ^ 2) := by
    simpa only [← pow_mul, Nat.mul_comm] using seven_square.pow k
  exact (hconj.symm.trans hpow).trans (hconj.pow 2)
private def certifiedEmbedding : SmallIndex.CertifiedStabilizer →* Carrier :=
  pointStabilizer.subtype.comp SmallIndex.pointStabilizerEquivCertified.symm.toMonoidHom
private theorem certifiedEmbedding_injective : Function.Injective certifiedEmbedding :=
  Subtype.val_injective.comp SmallIndex.pointStabilizerEquivCertified.symm.injective
private def eleven : Carrier := certifiedEmbedding SmallIndex.elevenElement
private theorem eleven_order : orderOf eleven = 11 := by
  exact (orderOf_injective certifiedEmbedding certifiedEmbedding_injective _).trans
    SmallIndex.elevenElement_order
private theorem eleven_four : IsConj eleven (eleven ^ 4) := by
  have h9 : IsConj eleven (eleven ^ 9) := by
    apply isConj_iff.mpr
    refine ⟨certifiedEmbedding SmallIndex.normalizerElement, ?_⟩
    simpa only [eleven, map_mul, map_inv, map_pow] using
      congrArg certifiedEmbedding SmallIndex.normalizerElement_conj
  have h81 := h9.trans (h9.pow 9)
  have he : eleven ^ 81 = eleven ^ 4 := by
    rw [← pow_mod_orderOf, eleven_order]
  simpa only [← pow_mul, he] using h81


/-- Every element of order eleven in the actual HS carrier is conjugate to its fourth power. -/
theorem orderEleven_fourthPower_fusion (g : Carrier)
    (hg : orderOf g = 11) : IsConj g (g ^ 4) := by
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := Carrier) (by decide : Nat.Prime 11)
    (by rw [NormalizerIndex.card_carrier]; decide) eleven_order hg
  have hconj : IsConj (eleven ^ k) g := isConj_iff.mpr ⟨c, hc.symm⟩
  have hpow : IsConj (eleven ^ k) ((eleven ^ k) ^ 4) := by
    simpa only [← pow_mul, Nat.mul_comm] using eleven_four.pow k
  exact (hconj.symm.trans hpow).trans (hconj.pow 4)

private theorem support_card_eq_of_prime_order {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card Carrier) (x g : Carrier)
    (hx : orderOf x = p) (hg : orderOf g = p) :
    (inclusion g).support.card = (inclusion x).support.card := by
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd hp hsq hx hg
  have hkp : ¬ p ∣ k := by
    intro hd
    have hxk : x ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx ▸ hd)
    have hg1 : g = 1 := by simp only [hxk, mul_one, mul_inv_cancel] at hc; exact hc
    exact hp.ne_one (by simpa only [hg1, orderOf_one] using hg.symm)
  have he : inclusion g = inclusion c * inclusion x ^ k * (inclusion c)⁻¹ := by
    rw [hc, map_mul, map_mul, map_inv, map_pow]
  rw [he, Equiv.Perm.card_support_conj, Equiv.Perm.support_pow_coprime]
  rw [orderOf_injective inclusion inclusion_injective, hx]
  exact (hp.coprime_iff_not_dvd.mpr hkp).symm

private theorem seven_support : (inclusion seven).support.card = 98 := by decide +kernel

private theorem eleven_support : (inclusion eleven).support.card = 99 := by
  have he : inclusion eleven = (SmallIndex.elevenElement : Equiv.Perm (Fin 100)) :=
    SmallIndex.pointStabilizerEquivCertified_symm_coe _
  rw [he]
  decide +kernel

/-- An order-seven carrier permutation fixes exactly two letters. -/
theorem orderSeven_fixed_card (g : Carrier) (hg : orderOf g = 7) :
    Fintype.card (Function.fixedPoints (inclusion g)) = 2 := by
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    support_card_eq_of_prime_order (by decide : Nat.Prime 7)
      (by rw [NormalizerIndex.card_carrier]; decide) seven g seven_order hg,
    seven_support]
  rfl

/-- An order-eleven carrier permutation fixes exactly one letter. -/
theorem orderEleven_fixed_card (g : Carrier) (hg : orderOf g = 11) :
    Fintype.card (Function.fixedPoints (inclusion g)) = 1 := by
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    support_card_eq_of_prime_order (by decide : Nat.Prime 11)
      (by rw [NormalizerIndex.card_carrier]; decide) eleven g eleven_order hg,
    eleven_support]
  rfl

private theorem fixed_of_commute_pair {x y : Equiv.Perm (Fin 100)}
    (hc : Commute x y) (hy : y ^ 11 = 1)
    (hx : Fintype.card (Function.fixedPoints x) = 2) :
    Function.fixedPoints x ⊆ Function.fixedPoints y := by
  let z : Equiv.Perm (Function.fixedPoints x) := y.subtypePerm
    (fun _ => Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm.eq))
  have hz11 : z ^ 11 = 1 := by
    dsimp only [z]
    rw [Equiv.Perm.subtypePerm_pow]
    apply Equiv.ext
    intro t
    apply Subtype.ext
    change (y ^ 11) t.val = t.val
    rw [hy]
    rfl
  have hzc : Nat.card (Equiv.Perm (Function.fixedPoints x)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hx]
    rfl
  have hz2 : z ^ 2 = 1 := hzc ▸ pow_card_eq_one' (x := z)
  have hzo : orderOf z ∣ 1 := by
    exact (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hz11))
  have hz : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hzo)
  intro t ht
  exact congrArg Subtype.val (congrArg (fun f : Equiv.Perm (Function.fixedPoints x) =>
    f ⟨t, ht⟩) hz)

/-- The literal HS carrier has no element of order 77. -/
theorem order_ne_seventySeven (g : Carrier) : orderOf g ≠ 77 := by
  intro hg
  have h7 : orderOf (g ^ 11) = 7 := by rw [orderOf_pow' _ (by decide), hg]; decide
  have h11 : orderOf (g ^ 7) = 11 := by rw [orderOf_pow' _ (by decide), hg]; decide
  have hc : Commute (inclusion (g ^ 11)) (inclusion (g ^ 7)) :=
    ((Commute.refl g).pow_pow 11 7).map inclusion
  have hf := fixed_of_commute_pair hc
    (by rw [← map_pow, ← h11, pow_orderOf_eq_one, map_one])
    (orderSeven_fixed_card (g ^ 11) h7)
  have hcard := Fintype.card_le_of_injective (Set.inclusion hf) (Set.inclusion_injective hf)
  rw [orderSeven_fixed_card _ h7, orderEleven_fixed_card _ h11] at hcard
  omega
end Sporadic.LeechRelated.HS.TracePowerFusion

