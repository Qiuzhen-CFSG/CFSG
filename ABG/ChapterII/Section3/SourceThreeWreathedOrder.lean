module

public import ABG.ChapterII.Section3.QProjectiveLinearComplement
public import ABG.ChapterII.Section3.CharacteristicPowerQuotient
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section2.SylowShapeTransport
public import GorensteinWalter.PGL2Cardinality
public import Theory.FieldTheory.OddQuadraticCoefficientLift

/-!
# The order of a characteristic-three wreathed Q-group modulo its odd core

A core-free Q-group of source characteristic three with a wreathed Sylow
subgroup of order 32 has order 96. The projective representation has kernel
its Sylow center, of order four. The coefficient group of a field of order
three is trivial, so the projective target has order 24. Conversely the
Sylow subgroup and the actual SL₂ constituent force divisibility by 32 and
24. Passing to the odd-core quotient preserves the Sylow presentation.

Source: ABG II.3 Proposition 3; Fong, J. Algebra 6 (1967), pp.70–71.
-/

namespace ABG
open GorensteinWalter

private theorem card_ringAut_three (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 3) : Nat.card (F ≃+* F) = 1 := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 3 1)
  let e : F ≃+* GaloisField 3 1 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide), pow_one]
      using hF)
  let : Subsingleton (GaloisField 3 1 ≃+* GaloisField 3 1) :=
    (Nat.card_eq_one_iff_unique.mp (GaloisField.card_ringAut 3 1 (by decide))).1
  have hsub : Subsingleton (F ≃+* F) := by
    refine ⟨fun a b => ?_⟩
    have hh : e.symm.trans (a.trans e) = e.symm.trans (b.trans e) := Subsingleton.elim _ _
    ext x
    have he := DFunLike.congr_fun hh (e x)
    simpa using e.injective he
  let := hsub
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

public theorem card_eq_96_of_corefree_sourceThree_wreathed32
    {H : Type*} [Group H] [Finite H]
    (hH : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : IsWreathedOfHeight S 2)
    (hq : HasSourceQCharacteristicPower H 3) : Nat.card H = 96 := by
  classical
  obtain ⟨F, iF, fF, hF, hFc, L0, hL0, ⟨eL0⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  let : L0.Characteristic := hL0
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let M := L0.map eQ.toMonoidHom
  let : M.Normal := (inferInstance : L0.Normal).map _ eQ.surjective
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F := (eQ.subgroupMap L0).symm.trans eL0
  let Z := subgroupCenter (S : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH S
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun x hx g => by
    have hh := Subgroup.mem_center_iff.mp (hZc hx) g
    simpa only [hh, mul_inv_cancel_right] using hx⟩
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  have hZcard : Nat.card Z = 4 := by
    change Nat.card ((Subgroup.center S).map (S : Subgroup H).subtype) = _
    rw [Subgroup.card_map_of_injective (S : Subgroup H).subtype_injective, P.card_center]
    norm_num
  obtain ⟨_, _, _, _, f, _, _, hfker, _⟩ :=
    qGroup_projective_linear_complement hH hcore S Z rfl M F hF eM
  have htarget : Nat.card (PGammaL2 F) = 24 := by
    rw [SemidirectProduct.card, pgl2_card_formula, card_ringAut_three F hFc, hFc]
    norm_num
  have hupper : Nat.card H ∣ 96 := by
    rw [← f.ker.card_mul_index, Subgroup.index_ker, hfker, hZcard]
    exact Nat.mul_dvd_mul_left 4 (htarget ▸ f.range.card_subgroup_dvd_card)
  have h32 : 32 ∣ Nat.card H := by
    have hh := (S : Subgroup H).card_subgroup_dvd_card
    norm_num [hS.2.1] at hh
    exact hh
  have h24 : 24 ∣ Nat.card H := by
    have hM : Nat.card M = 24 := by
      rw [Nat.card_congr eM.toEquiv, sl2_card_formula, hFc]
      norm_num
    exact hM ▸ M.card_subgroup_dvd_card
  apply Nat.dvd_antisymm hupper
  have hh := Nat.lcm_dvd h32 h24
  norm_num at hh
  exact hh

public theorem card_oddCore_quotient_eq_96_of_sourceThree_wreathed32
    {H : Type*} [Group H] [Finite H] (hH : IsQGroup H)
    (S : Sylow 2 H) (hS : IsWreathedOfHeight S 2)
    (hq : HasSourceQCharacteristicPower H 3) :
    Nat.card (H ⧸ pPrimeCore 2 H) = 96 := by
  let T := S.mapSurjective (f := QuotientGroup.mk' (pPrimeCore 2 H))
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := sylow_quotient_equiv S (pPrimeCore 2 H) pPrimeCore_coprime_card
  exact card_eq_96_of_corefree_sourceThree_wreathed32 hH.oddCore_quotient
    (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2)) T (wreathed_equiv e hS)
    hq.oddCore_quotient

end ABG
