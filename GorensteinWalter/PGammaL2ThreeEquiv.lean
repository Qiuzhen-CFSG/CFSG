module

public import GorensteinWalter.PGammaL2Subgroups
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv

/-!
# The projective semilinear group over a field of order three

For any field of order three, its projective semilinear group is the actual
symmetric group on four letters. Transport from `ZMod 3` shows that every
coefficient automorphism is trivial. Hence the linear inclusion is an
isomorphism, and the projective-line action gives the required symmetric
group model.

This supplies the characteristic-three target for ABG II.3's projective
Q-group map, used in Fong's order-32 centralizer calculation (1967, p. 71).
The exceptional linear isomorphism is proved in `LinearThreeEquiv`.
-/

namespace GorensteinWalter

/-- Coefficient automorphisms contribute nothing over a field of order three. -/
public noncomputable def pGammaL2_three_equiv_perm
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 3) :
    PGammaL2 K ≃* Equiv.Perm (Fin 4) := by
  let := Fintype.ofFinite K
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have hAut : Subsingleton (K ≃+* K) := by
    constructor
    intro a b
    ext x
    obtain ⟨z, rfl⟩ := e.surjective x
    exact DFunLike.congr_fun (Subsingleton.elim (e.trans a) (e.trans b)) z
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  have hi : Function.Bijective i := by
    refine ⟨SemidirectProduct.inl_injective, ?_⟩
    intro x
    refine ⟨x.left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hAut.elim _ _
  exact (MulEquiv.ofBijective i hi).symm.trans
    ((pgl2RingEquiv e).symm.trans pgl2_three_equiv_perm)

public theorem pGammaL2_card_three (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 3) : Nat.card (PGammaL2 K) = 24 := by
  rw [Nat.card_congr (pGammaL2_three_equiv_perm K hK).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-- A subgroup containing the projective special linear layer and an order-eight
subgroup is the whole characteristic-three projective semilinear group. -/
public theorem pGammaL2_eq_top_of_card_three_of_eight_dvd
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 3)
    (A : Subgroup (PGammaL2 K)) (hPSL : pGammaL2PSLRange K ≤ A)
    (h8 : 8 ∣ Nat.card A) : A = ⊤ := by
  let e := pGammaL2_three_equiv_perm K hK
  let : Finite (PGammaL2 K) := Finite.of_injective e e.injective
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨3, 1, Nat.prime_three, by decide, by decide, by simpa using hK⟩
  have h12 : Nat.card (pGammaL2PSLRange K) = 12 := by
    rw [← Nat.card_congr (pGammaL2PSLRangeEquiv K).toEquiv,
      psl2_card_formula K hodd, hK]
    decide
  have h12dvd : 12 ∣ Nat.card A := h12 ▸ Subgroup.card_dvd_of_le hPSL
  have h24dvd : 24 ∣ Nat.card A := by
    have h : Nat.lcm 12 8 = 24 := by decide
    simpa only [h] using Nat.lcm_dvd h12dvd h8
  apply Subgroup.eq_top_of_card_eq
  rw [pGammaL2_card_three K hK]
  apply le_antisymm
  · have h := Subgroup.card_le_of_le (show A ≤ ⊤ from le_top)
    simpa only [Subgroup.card_top, pGammaL2_card_three K hK] using h
  · exact Nat.le_of_dvd Nat.card_pos h24dvd

end GorensteinWalter
