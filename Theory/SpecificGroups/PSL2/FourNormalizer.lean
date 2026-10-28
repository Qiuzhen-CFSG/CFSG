module
public import Theory.SpecificGroups.PSL2.FourNormalizer.Cubic
public import Theory.GroupTheory.FourNormalizerOfCubic
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers

/-!
# Four-normalizers in odd PSL₂ with two-part at least eight

The projective-linear self-centralizer theorem gives C(F)=F. The explicit
quaternion matrix supplies a cubic automizer, while Sylow normalizer
congruence supplies a factor of eight. Thus the normalizer has order 24
and its normal self-centralizing four-group identifies it with S₄.
For prime fields the order formula supplies the required two-part whenever
p is 1 or -1 modulo eight, expressed as divisibility of p-1 or p+1.

This proves the intrinsic prime-linear case of Aschbacher–Smith 2.5.8(5),
printed pp.556–557, on the actual quotient of SL₂ by its center.
-/

public section
open Subgroup Matrix GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2.FourNormalizer
variable {K : Type*} [Field K] [Finite K]

/-- Self-centrality on the actual PSL₂ carrier, obtained through its injection into PGL₂. -/
theorem four_centralizer (hK : IsOddPrimePower (Nat.card K))
    (F : Subgroup PSL(2,K)) [IsKleinFour F] : centralizer (F : Set PSL(2,K)) = F := by
  let f : PSL(2,K) →* PGL2 K := ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := ProjectiveSpecialLinearGroup.toPGL_injective
  let A := F.map f
  let e := F.equivMapOfInjective f hf
  let hA : IsKleinFour A :=
    { card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans IsKleinFour.exponent_two }
  have hc := pgl2_kleinFour_centralizer_eq_self K hK A hA
  let : IsMulCommutative F := IsKleinFour.isMulCommutative
  apply le_antisymm _ F.le_centralizer
  intro x hx
  have hm : f x ∈ centralizer (A : Set (PGL2 K)) :=
    map_centralizer_le_centralizer_image (F : Set PSL(2,K)) f ⟨x,hx,rfl⟩
  rw [hc] at hm
  exact (mem_map_iff_mem hf).mp hm

/-- Every four-group has normalizer S₄ once eight divides the order of odd PSL₂. -/
theorem four_normalizer (hK : IsOddPrimePower (Nat.card K))
    (h8 : 8 ∣ Nat.card PSL(2,K)) (F : Subgroup PSL(2,K)) [IsKleinFour F] :
    Nonempty (normalizer (F : Set PSL(2,K)) ≃* Equiv.Perm (Fin 4)) := by
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p,n,_,hp,_,he⟩ := hK
    rw [he]
    exact hp.pow
  have h2 : (2 : K) ≠ 0 := by
    let : Fintype K := Fintype.ofFinite K
    apply Ring.two_ne_zero
    intro hchar
    have heven := FiniteField.even_card_of_char_two (F := K) hchar
    have hodd' : Odd (Fintype.card K) := by simpa only [Nat.card_eq_fintype_card] using hodd
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_iff.mpr heven)
  exact Theory.GroupTheory.four_normalizer_equiv_of_cubic F (four_centralizer hK F) h8
    (three_dvd_four_normalizer h2 F)

private theorem prime_eight_dvd_order {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (h8 : 8 ∣ p - 1 ∨ 8 ∣ p + 1) : 8 ∣ Nat.card PSL(2,ZMod p) := by
  have hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,Fact.out,hp,by decide,by simp⟩
  rw [psl2_card_formula (ZMod p) hK, Nat.card_zmod]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hprod : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    nlinarith [Nat.sub_add_cancel hp1, Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  rw [hprod]
  have hm : 2 ∣ p - 1 := by obtain ⟨k,hk⟩ := hp; exact ⟨k,by omega⟩
  have ha : 2 ∣ p + 1 := by obtain ⟨k,hk⟩ := hp; exact ⟨k+1,by omega⟩
  have h16 : 16 ∣ (p - 1) * (p + 1) := by
    rcases h8 with h | h
    · exact Nat.mul_dvd_mul h ha
    · exact Nat.mul_dvd_mul hm h
  have h16p : 16 ∣ p * ((p - 1) * (p + 1)) := dvd_mul_of_dvd_right h16 p
  exact (Nat.dvd_div_iff_mul_dvd ((by decide : 2 ∣ 16).trans h16p)).mpr h16p

/-- The prime-field family p ≡ ±1 modulo eight; in particular it includes every
large Fermat or Mersenne prime in the source's remaining catalogue. -/
theorem prime_four_normalizer (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (h8 : 8 ∣ p - 1 ∨ 8 ∣ p + 1) (F : Subgroup PSL(2,ZMod p)) [IsKleinFour F] :
    Nonempty (normalizer (F : Set PSL(2,ZMod p)) ≃* Equiv.Perm (Fin 4)) :=
  four_normalizer (K := ZMod p) ⟨p,1,Fact.out,hp,by decide,by simp⟩
    (prime_eight_dvd_order (p := p) hp h8) F

end Theory.PSL2.FourNormalizer
