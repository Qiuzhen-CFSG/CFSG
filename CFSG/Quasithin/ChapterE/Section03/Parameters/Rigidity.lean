module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Centralizer rigidity below the global parameter s

If `B ≤ V` has corank below `s(G,V)`, every two-subgroup `E` satisfies
`C_E(B) = C_E(V)`. Consequently `B ≤ A ≤ V` gives the two equalities in E.3.6.
The printed invariance assumption is retained in the source wrapper, although
this argument does not need it.

The bound by `r` puts `C_E(B)` inside `N_G(V)`. Its actual image in `Aut_G(V)`
is a two-group fixing `B`, so its fixed-space codimension is at most the corank
of `B`. A nontrivial image would contain an involution and force this codimension
to be at least the local parameter `m`, contradicting the bound by `s`.
Triviality of the image then gives centralization via the normalizer action's
kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma E.3.6,
printed p. 232 (PDF p. 243).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem rigidity_fixedCodim_le_corank
    (V B : Subgroup G) [IsElementaryAbelian 2 V] (I : Subgroup (Automizer V))
    (hfix : ∀ (b : V), (b : G) ∈ B → ∀ a : I,
      automizerRepresentation V (a : Automizer V) (Additive.ofMul b) = Additive.ofMul b) :
    fixedCodim (automizerRepresentation V) I ≤ subgroupCorank V B := by
  let S : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (B.subgroupOf V).toAddSubgroup
  have hS : S ≤ fixedSpace (automizerRepresentation V) I := by
    intro b hb
    exact hfix b hb
  have hdim := Submodule.finrank_mono hS
  have hsum := fixedCodim_add_finrank (automizerRepresentation V) I
  have hcardS : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at h
    simpa only [Nat.card_zmod] using h
  have hcardB : Nat.card (B.subgroupOf V) = Nat.card S := rfl
  have hindex : (B.subgroupOf V).index = 2 ^ subgroupCorank V B := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact V.relIndex_eq_two_pow_quotient_finrank B
  have hc := (B.subgroupOf V).card_mul_index
  rw [hcardB, hcardS, hindex, hcardV, ← pow_add] at hc
  have he := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
  omega

omit [Finite G] in
private theorem rigidity_induced_fixed (V B C : Subgroup G)
    [IsElementaryAbelian 2 V] (hCB : C ≤ centralizer (B : Set G))
    (b : V) (hb : (b : G) ∈ B) (a : inducedAutomizer V C) :
    automizerRepresentation V (a : Automizer V) (Additive.ofMul b) = Additive.ofMul b := by
  obtain ⟨c, hc, he⟩ := Subgroup.mem_map.mp a.property
  change V.normalizerMonoidHom.rangeRestrict c = (a : Automizer V) at he
  rw [← he]
  change V.normalizerMonoidHom c b = b
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hcomm := (Subgroup.mem_centralizer_iff.mp (hCB hc)) (b : G) hb
  change (b : G) * (c : G) = (c : G) * (b : G) at hcomm
  rw [← hcomm, mul_inv_cancel_right]

/-- The two-group centralizer is already the centralizer of all of `V`. -/
theorem centralizer_inf_eq_of_corank_lt_globalS
    {V B E : Subgroup G} [IsElementaryAbelian 2 V]
    (hBV : B ≤ V) (hB : (subgroupCorank V B : ℕ∞) < globalS V)
    (hE : IsPGroup 2 E) :
    E ⊓ centralizer (B : Set G) = E ⊓ centralizer (V : Set G) := by
  let C := E ⊓ centralizer (B : Set G)
  have hCN : C ≤ normalizer (V : Set G) := inf_le_right.trans
    (centralizer_le_normalizer_of_corank_lt_globalR hBV
      (hB.trans_le (globalS_le_globalR V)))
  let I := inducedAutomizer V C
  have hIp : IsPGroup 2 I := hE.to_inf_left.comap_subtype.map
    V.normalizerMonoidHom.rangeRestrict
  have hdim : fixedCodim (automizerRepresentation V) I ≤ subgroupCorank V B :=
    rigidity_fixedCodim_le_corank V B I (rigidity_induced_fixed V B C inf_le_right)
  have hI : I = ⊥ := by
    by_contra hn
    let _ : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).mpr hn
    obtain ⟨n, hn, hc⟩ := hIp.nontrivial_iff_card.mp inferInstance
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
      (hc ▸ dvd_pow_self 2 (by omega : n ≠ 0))
    have ht' : orderOf (t : Automizer V) = 2 := (Subgroup.orderOf_coe t).trans ht
    have hm : localM V ≤ fixedCodim (automizerRepresentation V) I :=
      (moduleM_le_involution (automizerRepresentation V) ht').trans
        (fixedCodim_mono (automizerRepresentation V)
          (Subgroup.zpowers_le.mpr t.property))
    have hlt : subgroupCorank V B < localM V :=
      ENat.natCast_lt_natCast.mp (hB.trans_le (globalS_le_localM V))
    omega
  have hCV : C ≤ centralizer (V : Set G) := by
    intro c hc
    let cN : normalizer (V : Set G) := ⟨c, hCN hc⟩
    have hi : V.normalizerMonoidHom.rangeRestrict cN ∈ I :=
      Subgroup.mem_map.mpr ⟨cN, hc, rfl⟩
    have hone := Subgroup.mem_bot.mp (hI ▸ hi)
    have hk : cN ∈ V.normalizerMonoidHom.ker := by
      change V.normalizerMonoidHom cN = 1
      exact congrArg Subtype.val hone
    rwa [Subgroup.normalizerMonoidHom_ker] at hk
  exact le_antisymm (le_inf inf_le_left hCV)
    (inf_le_inf_left E (Subgroup.centralizer_le hBV))

/-- Centralizer rigidity below `s`, without the unused invariance hypothesis. -/
theorem centralizer_rigidity_of_corank_lt_globalS
    {V A B E : Subgroup G} [IsElementaryAbelian 2 V]
    (hBA : B ≤ A) (hAV : A ≤ V)
    (hB : (subgroupCorank V B : ℕ∞) < globalS V) (hE : IsPGroup 2 E) :
    E ⊓ centralizer (A : Set G) = E ⊓ centralizer (B : Set G) ∧
      E ⊓ centralizer (B : Set G) = E ⊓ centralizer (V : Set G) := by
  have heq := centralizer_inf_eq_of_corank_lt_globalS (hBA.trans hAV) hB hE
  refine ⟨le_antisymm (inf_le_inf_left E (Subgroup.centralizer_le hBA)) ?_, heq⟩
  rw [heq]
  exact inf_le_inf_left E (Subgroup.centralizer_le hAV)

/-- Aschbacher–Smith E.3.6, including the section's nontriviality assumption
and the printed `A`-invariance hypothesis. -/
theorem lemma_E_3_6
    {V A B E : Subgroup G} [IsElementaryAbelian 2 V]
    (_hV : V ≠ ⊥) (hBA : B ≤ A) (hAV : A ≤ V)
    (hB : (subgroupCorank V B : ℕ∞) < globalS V)
    (_hAE : A ≤ normalizer (E : Set G)) (hE : IsPGroup 2 E) :
    E ⊓ centralizer (A : Set G) = E ⊓ centralizer (B : Set G) ∧
      E ⊓ centralizer (B : Set G) = E ⊓ centralizer (V : Set G) :=
  centralizer_rigidity_of_corank_lt_globalS hBA hAV hB hE

end CFSG.Quasithin.ChapterE
