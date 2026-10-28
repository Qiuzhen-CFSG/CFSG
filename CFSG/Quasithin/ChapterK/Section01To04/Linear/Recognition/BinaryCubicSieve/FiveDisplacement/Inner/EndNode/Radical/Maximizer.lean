module

public import Theory.Representation.BinaryOffender.CubicEndField
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.GeneratedSubgroupInvariants
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness

/-!
# Promoting a squared offender inside a minimal normal subgroup

Maximize |B|² |C_V(B)| over the subgroups of a fixed normal subgroup U,
then choose a maximizer of largest order. Supermodularity makes it contain
all maximizers. Conjugation preserves both U and the objective, so that
largest maximizer is normal in the acting group. If U is minimal normal,
a nontrivial offender therefore makes U itself an offender.

This is the relative form of the maximization argument in
`Theory.Representation.BinaryOffender.TwoFCardBound`, adapted without changing
that shared module. It supplies the radical-enlargement step of Guralnick–Malle,
*Classification of 2F-modules, II*, Lemma 2.1 and Proposition 4.7, step 1,
manuscript pp.5 and 25. Cubicity need not survive this enlargement and is
not asserted to do so.
-/

public section
open Representation Representation.BinaryOffender Subgroup

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.RadicalMaximizer
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private noncomputable def measure (B : Subgroup G) : ℕ := Nat.card B ^ 2 * Nat.card (fixedSpace ρ B)

private theorem group_card_inequality (B C : Subgroup G) :
    Nat.card B * Nat.card C ≤
      Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
  have hi := Subgroup.relIndex_le_of_le_right (H := B)
    (show C ≤ B ⊔ C from le_sup_right) (B.subgroupOf (B ⊔ C)).index_ne_zero_of_finite
  have hC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ C) C
    bot_le inf_le_right
  have hBC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) B (B ⊔ C)
    bot_le le_sup_left
  simp only [Subgroup.relIndex_bot_left] at hC hBC
  rw [Subgroup.inf_relIndex_right] at hC
  calc
    Nat.card B * Nat.card C =
        Nat.card (B ⊓ C : Subgroup G) * (Nat.card B * B.relIndex C) := by
          rw [← hC]; ac_rfl
    _ ≤ Nat.card (B ⊓ C : Subgroup G) * (Nat.card B * B.relIndex (B ⊔ C)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi)
    _ = _ := by rw [hBC]

private theorem measure_supermodular (B C : Subgroup G) :
    measure ρ B * measure ρ C ≤ measure ρ (B ⊓ C) * measure ρ (B ⊔ C) := by
  have hd := ρ.finrank_invariants_sup_lower_bound B C (B ⊓ C) inf_le_left inf_le_right
  have hf : Nat.card (fixedSpace ρ B) * Nat.card (fixedSpace ρ C) ≤
      Nat.card (fixedSpace ρ (B ⊓ C)) * Nat.card (fixedSpace ρ (B ⊔ C)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ B),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ C),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (B ⊓ C)),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (B ⊔ C)),
      Nat.card_zmod, ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) hd
  have hh := Nat.mul_le_mul (Nat.pow_le_pow_left (group_card_inequality B C) 2) hf
  dsimp [measure]
  convert hh using 1 <;> ring

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem measure_conj (B : Subgroup G) (g : G) :
    measure ρ (B.map (MulAut.conj g).toMonoidHom) = measure ρ B := by
  unfold measure
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    ← Nat.card_congr (fixedSpaceConjEquiv ρ B g).toEquiv]

private theorem exists_largest_relative_maximizer (U : Subgroup G) :
    ∃ K : Subgroup G, K ≤ U ∧ (∀ B, B ≤ U → measure ρ B ≤ measure ρ K) ∧
      (∀ B, B ≤ U → measure ρ B = measure ρ K → B ≤ K) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨D, hDU, hD⟩ := Set.exists_max_image {B : Subgroup G | B ≤ U}
    (measure ρ) (Set.toFinite _) ⟨⊥, show (⊥ : Subgroup G) ≤ U from bot_le⟩
  let S : Set (Subgroup G) := {B | B ≤ U ∧ measure ρ B = measure ρ D}
  obtain ⟨K, hK, hcard⟩ := Set.exists_max_image S (fun B => Nat.card B)
    (Set.toFinite _) ⟨D, hDU, rfl⟩
  have hmax (B : Subgroup G) (hBU : B ≤ U) : measure ρ B ≤ measure ρ K := by
    rw [hK.2]
    exact hD B hBU
  refine ⟨K, hK.1, hmax, ?_⟩
  intro B hBU hB
  have hpos : 0 < measure ρ K := Nat.mul_pos (pow_pos Nat.card_pos 2) Nat.card_pos
  have hjoin : measure ρ (K ⊔ B) = measure ρ K := by
    apply le_antisymm (hmax _ (sup_le hK.1 hBU))
    have hi := measure_supermodular ρ K B
    rw [hB] at hi
    have hu := Nat.mul_le_mul_right (measure ρ (K ⊔ B))
      (hmax (K ⊓ B) (inf_le_left.trans hK.1))
    exact Nat.le_of_mul_le_mul_left (hi.trans hu) hpos
  have he : K = K ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hcard (K ⊔ B) ⟨sup_le hK.1 hBU, hjoin.trans hK.2⟩)
  exact he ▸ le_sup_right

/-- A nontrivial squared offender inside a minimal normal elementary subgroup
makes the whole subgroup a squared offender. Normality is in G, the group
acting in this lemma; in the end-node application G is the parabolic. -/
theorem fixedCodim_le_twice_rank_of_minimal_normal
    (U : Subgroup G) [U.Normal] (hU : IsElementaryTwo U)
    (hminimal : ∀ K : Subgroup G, K.Normal → K ≤ U → K = ⊥ ∨ K = U)
    {A : Subgroup G} (hAU : A ≤ U) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    fixedCodim ρ U ≤ 2 * rank U := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨K, hKU, hmax, hlarge⟩ := exists_largest_relative_maximizer ρ U
  have hbound : Nat.card V ≤ measure ρ A :=
    (fixedCodim_le_mul_rank_iff_card_pow ρ A hA 2).mp hsmall
  have hbot : measure ρ ⊥ = Nat.card V := by
    simp [measure, fixedSpace_bot]
  have hKne : K ≠ ⊥ := by
    intro hK
    have he : measure ρ A = measure ρ K :=
      le_antisymm (hmax A hAU) (by rw [hK, hbot]; exact hbound)
    exact hA.1 (bot_unique (hK ▸ hlarge A hAU he))
  let : K.Normal := ⟨fun n hn g => by
    have hconj : K.map (MulAut.conj g).toMonoidHom ≤ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (inferInstance : U.Normal).conj_mem x (hKU hx) g
    exact hlarge (K.map (MulAut.conj g).toMonoidHom) hconj (measure_conj ρ K g)
      (Subgroup.mem_map_of_mem _ hn)⟩
  have hKUeq : K = U := (hminimal K inferInstance hKU).resolve_left hKne
  apply (fixedCodim_le_mul_rank_iff_card_pow ρ U hU 2).mpr
  change Nat.card V ≤ measure ρ U
  rw [← hKUeq]
  exact hbound.trans (hmax A hAU)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.RadicalMaximizer
