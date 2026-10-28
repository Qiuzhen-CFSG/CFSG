module

public import ABG.ChapterII.Section3.QProjectiveLinearComplement
public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import ABG.ChapterII.Section1.WreathedCenter
public import GorensteinWalter.PGammaL2ThreeEquiv

/-!
# The characteristic-three projective quotient of a wreathed Q-group

A Q-group with trivial odd core, a wreathed Sylow subgroup of order 32, and source
characteristic power three has order 96. Its quotient by the center of
the supplied Sylow subgroup is the actual symmetric group on four letters.
The projective epimorphism retains that exact kernel.

ABG's projective map has the Sylow center, of order four, as kernel. Its
range contains PSL₂(3), of order twelve, and has order divisible by eight
because the original group contains the order-32 Sylow subgroup. These
divisibilities force its range to be all of PGammaL₂(3), which is S₄.
Transport the prescribed characteristic SL₂ constituent through the
trivial odd-core quotient to apply this argument.

Sources: ABG II.3 Proposition 3, article pp. 25–27; Fong (1967), p. 71,
the centralizer quotients immediately preceding equation (6).
-/

namespace ABG
open GorensteinWalter
universe u

private theorem projective_of_normal_sl2
    {H F : Type u} [Group H] [Finite H] [Field F] [Finite F]
    (hQ : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : IsWreathedOfHeight S 2)
    (L0 : Subgroup H) [L0.Normal] (hF : Nat.card F = 3)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nat.card H = 96 ∧ ∃ f : H →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = subgroupCenter (S : Subgroup H) := by
  let Z := subgroupCenter (S : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hQ S
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 1, Nat.prime_three, by decide, by decide, by simpa using hF⟩
  obtain ⟨_, _, _, _, f, L, E, hker, _, _, _, _, _, _, hL0, _⟩ :=
    qGroup_projective_linear_complement_with_core_map hQ hcore S Z rfl L0 F hFodd eL0
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  have hZcard : Nat.card Z = 4 := by
    rw [show Z = (Subgroup.center S).map (S : Subgroup H).subtype from rfl,
      Subgroup.card_map_of_injective (S : Subgroup H).subtype_injective, P.card_center]
    decide
  have hcard : Nat.card H = Nat.card f.range * 4 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker, hZcard]
  have h32 : 32 ∣ Nat.card H := by
    have h := (S : Subgroup H).card_subgroup_dvd_card
    simpa only [hS.2.1, show 2 ^ (2 * 2 + 1) = 32 from rfl] using h
  have h8 : 8 ∣ Nat.card f.range := by
    obtain ⟨k, hk⟩ := h32
    refine ⟨k, ?_⟩
    omega
  have hPSL : pGammaL2PSLRange F ≤ f.range := by
    rw [← hL0]
    exact L0.map_le_range f
  have htop : f.range = ⊤ := pGammaL2_eq_top_of_card_three_of_eight_dvd F hF f.range hPSL h8
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp htop
  have hHcard : Nat.card H = 96 := by
    simpa only [htop, Subgroup.card_top, pGammaL2_card_three F hF] using hcard
  let e := pGammaL2_three_equiv_perm F hF
  refine ⟨hHcard, e.toMonoidHom.comp f, e.surjective.comp hf, ?_⟩
  rw [MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective]
  exact hker

/-- The actual projective epimorphism of a characteristic-three wreathed Q-group. -/
public theorem qGroup_wreathed32_sourceThree_projective
    {H : Type u} [Group H] [Finite H]
    (hQ : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : IsWreathedOfHeight S 2)
    (hq : HasSourceQCharacteristicPower H 3) :
    Nat.card H = 96 ∧ ∃ f : H →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = subgroupCenter (S : Subgroup H) := by
  obtain ⟨F, iF, fF, _, hF, L0, hL0, ⟨eL0⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  let : L0.Characteristic := hL0
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let M := L0.map eQ.toMonoidHom
  let : M.Normal := (inferInstance : L0.Normal).map _ eQ.surjective
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F := (eQ.subgroupMap L0).symm.trans eL0
  exact projective_of_normal_sl2 hQ hcore S hS M hF eM

end ABG
