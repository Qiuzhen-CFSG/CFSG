module

public import Stellmacher.MainDefs
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Trivial two-core modulo the odd core in the multiple-maximal branch

Let `S0` be a Sylow 2-subgroup of a finite group `H`. If every two-local
overgroup of `S0` has characteristic two and two distinct maximal two-locals
contain `S0`, then `H / O_{2'}(H)` has trivial two-core. No solvability,
Baumann-local hypothesis, or terminal classification is needed.

The odd core of a characteristic-two local is trivial: it centralizes the
two-core by the imported coprime normal-subgroup argument, and characteristic
two puts it inside that two-core. The intersection with the ambient odd core
is a normal odd subgroup of the local, so the quotient map is injective on
each such local. The quotient two-core lies in the image Sylow. Intersecting
its inverse image with `S0` gives a two-subgroup mapping onto the quotient
two-core. Injectivity on each local lifts conjugates back into this same
subgroup. If it were nontrivial, its normalizer would be a common two-local
overgroup, contradicting maximality and distinctness.

This is an elementary reduction for the multiple-maximal configuration in
`refs/latex/stellmacher-n-group.tex`, Sections 5 and 11, rather than a claim
that the source proves Sylow Baumann stability. The odd-core argument follows
the pattern in `Stellmacher.CharacteristicTwoNormal`; only the required
centralization API is imported here.
-/

namespace Stellmacher.SectionEleven

private theorem local_quotient_injective
    {H : Type*} [Group H] [Finite H] (U : Subgroup H)
    (hchar : Stellmacher.IsCharacteristicTwoType U) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 H)).comp U.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : pPrimeCore 2 U = ⊥ := by
    have hle : pPrimeCore 2 U ≤ pCore 2 U :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 U)
        (pCore_isPGroup (p := 2) (G := U))).trans hchar
    obtain ⟨power, hpower⟩ := (pCore_isPGroup (p := 2) (G := U)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 U)) (Nat.card (pPrimeCore 2 U)) := by
      rw [hpower]
      exact (pPrimeCore_coprime_card (p := 2) (G := U)).pow_left power
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot)
  have hinter : (pPrimeCore 2 H).comap U.subtype ≤ pPrimeCore 2 U := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ U.subtype_injective)
      (pPrimeCore_coprime_card (p := 2) (G := H))
  apply (injective_iff_map_eq_one _).mpr
  intro element helement
  have hmem : element ∈ (pPrimeCore 2 H).comap U.subtype :=
    (QuotientGroup.eq_one_iff (N := pPrimeCore 2 H) (element : H)).mp helement
  have hbot : element ∈ (⊥ : Subgroup U) := hodd ▸ hinter hmem
  exact hbot

/-- Two distinct characteristic-two maximal locals over a Sylow force the
two-core of the quotient by the ambient odd core to be trivial. -/
public theorem twoCore_oddCore_quotient_eq_bot_of_multiple_maximal
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S0 : Subgroup H) ≤ U →
      Stellmacher.IsCharacteristicTwoType U)
    (hmultiple : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    pCore 2 (H ⧸ pPrimeCore 2 H) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  let core := pCore 2 (H ⧸ pPrimeCore 2 H)
  let lift : Subgroup H := (S0 : Subgroup H) ⊓ core.comap quotient
  have hcore : core ≤ (S0 : Subgroup H).map quotient :=
    (pCore_isPGroup (p := 2) (G := H ⧸ pPrimeCore 2 H)).le_sylow_of_normal
      (S0.mapSurjective (QuotientGroup.mk'_surjective _))
  have hmap : lift.map quotient = core := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr inf_le_right
    · intro element helement
      obtain ⟨preimage, hpreimage, rfl⟩ := hcore helement
      exact ⟨preimage, ⟨hpreimage, helement⟩, rfl⟩
  by_contra hnontrivial
  have hlift : lift ≠ ⊥ := by
    intro hbot
    apply hnontrivial
    change core = ⊥
    rw [← hmap, hbot, Subgroup.map_bot]
  have htwo : IsPGroup 2 lift :=
    S0.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  obtain ⟨M1, M2, hne, hmax1, hmax2, hS1, hS2⟩ := hmultiple
  have hnormalizer (U : Subgroup H) (hU : IsTwoLocal U)
      (hSU : (S0 : Subgroup H) ≤ U) : U ≤ Subgroup.normalizer (lift : Set H) := by
    have hinj := local_quotient_injective U (hlocal U hU hSU)
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    have hconj : quotient (actor * element * actor⁻¹) ∈ core := by
      simp only [map_mul, map_inv]
      exact Subgroup.Normal.conj_mem inferInstance _ helement.2 _
    obtain ⟨preimage, hpreimage, heq⟩ := hcore hconj
    have heqU : (⟨preimage, hSU hpreimage⟩ : U) =
        ⟨actor * element * actor⁻¹,
          U.mul_mem (U.mul_mem hactor (hSU helement.1)) (U.inv_mem hactor)⟩ :=
      hinj heq
    have heqH : preimage = actor * element * actor⁻¹ := congrArg Subtype.val heqU
    exact ⟨heqH ▸ hpreimage, hconj⟩
  have hN : IsTwoLocal (Subgroup.normalizer (lift : Set H)) :=
    ⟨lift, hlift, htwo, rfl⟩
  have hle1 := hnormalizer M1 hmax1.1 hS1
  have hle2 := hnormalizer M2 hmax2.1 hS2
  exact hne ((le_antisymm hle1 (hmax1.2 hN hle1)).trans
    (le_antisymm hle2 (hmax2.2 hN hle2)).symm)

end Stellmacher.SectionEleven
