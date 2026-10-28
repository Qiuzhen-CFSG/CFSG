module

public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.GeneratedSubgroupInvariants
public import Mathlib.GroupTheory.Index

/-!
# Ratio-two maximization inside a normalizer-irreducible subgroup

Maximize |B|² |C_V(B)| over the subgroups of U, and choose a maximizer M
of largest order. The subgroup index inequality and the fixed-space dimension
formula show that M contains every maximizer. Hence N_G(U) normalizes M.
A nontrivial ratio-two subgroup ensures M is nontrivial. If N_G(U) has no
nontrivial proper invariant subgroup in U, then M=U and U inherits the bound.

This is Guralnick–Malle, Classification of 2F-modules II, Lemmas 2.1–2.2,
applied in Proposition 4.1 to the unipotent subgroup of binary SL₂. The actual
SL₂ application is in Chapter K's PSL2Recognition.DegreeSelection.Inner.
-/

public section
open Representation Subgroup
namespace Representation.BinaryOffender
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

private noncomputable def measure (B : Subgroup H) : ℕ :=
  Nat.card B ^ 2 * Nat.card (fixedSpace ρ B)

private theorem group_card_inequality (B C : Subgroup H) :
    Nat.card B * Nat.card C ≤
      Nat.card (B ⊓ C : Subgroup H) * Nat.card (B ⊔ C : Subgroup H) := by
  have hi := Subgroup.relIndex_le_of_le_right (H := B)
    (show C ≤ B ⊔ C from le_sup_right) (B.subgroupOf (B ⊔ C)).index_ne_zero_of_finite
  have hC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup H) (B ⊓ C) C
    bot_le inf_le_right
  have hBC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup H) B (B ⊔ C)
    bot_le le_sup_left
  simp only [Subgroup.relIndex_bot_left] at hC hBC
  rw [Subgroup.inf_relIndex_right] at hC
  calc
    Nat.card B * Nat.card C =
        Nat.card (B ⊓ C : Subgroup H) * (Nat.card B * B.relIndex C) := by
          rw [← hC]; ac_rfl
    _ ≤ Nat.card (B ⊓ C : Subgroup H) * (Nat.card B * B.relIndex (B ⊔ C)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi)
    _ = _ := by rw [hBC]

private theorem measure_supermodular (B C : Subgroup H) :
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

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem measure_conj (B : Subgroup H) (g : H) :
    measure ρ (B.map (MulAut.conj g).toMonoidHom) = measure ρ B := by
  unfold measure
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    ← Nat.card_congr (fixedSpaceConjEquiv ρ B g).toEquiv]

private theorem exists_largest_maximizer (U : Subgroup H) :
    ∃ M ≤ U, (∀ B ≤ U, measure ρ B ≤ measure ρ M) ∧
      (∀ B ≤ U, measure ρ B = measure ρ M → B ≤ M) := by
  classical
  let : Finite W := Module.finite_of_finite (ZMod 2)
  obtain ⟨D, hDU, hD⟩ := Set.exists_max_image {B : Subgroup H | B ≤ U}
    (measure ρ) (Set.toFinite _) ⟨U, show U ≤ U from le_rfl⟩
  let S : Set (Subgroup H) := {B | B ≤ U ∧ measure ρ B = measure ρ D}
  obtain ⟨M, hM, hcard⟩ := Set.exists_max_image S (fun B => Nat.card B)
    (Set.toFinite _) ⟨D, hDU, rfl⟩
  have hmax (B : Subgroup H) (hBU : B ≤ U) : measure ρ B ≤ measure ρ M := by
    rw [show measure ρ M = measure ρ D from hM.2]
    exact hD B hBU
  refine ⟨M, hM.1, hmax, ?_⟩
  intro B hBU hB
  have hpos : 0 < measure ρ M := Nat.mul_pos (pow_pos Nat.card_pos 2) Nat.card_pos
  have hjoin : measure ρ (M ⊔ B) = measure ρ M := by
    apply le_antisymm (hmax _ (sup_le hM.1 hBU))
    have hi := measure_supermodular ρ M B
    rw [hB] at hi
    have hu := Nat.mul_le_mul_right (measure ρ (M ⊔ B))
      (hmax (M ⊓ B) (inf_le_left.trans hM.1))
    exact Nat.le_of_mul_le_mul_left (hi.trans hu) hpos
  have he : M = M ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hcard (M ⊔ B) ⟨sup_le hM.1 hBU, hjoin.trans hM.2⟩)
  exact he ▸ le_sup_right

/-- If the normalizer of U has no nontrivial proper invariant subgroup of U,
an elementary ratio-two actor inside U makes U itself a ratio-two actor.
Neither U nor its normalizer is assumed to act irreducibly on the module. -/
theorem card_le_of_ratio_two_of_normalizer_irreducible (U A : Subgroup H) (hAU : A ≤ U)
    (hA : IsElementaryTwo A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hirr : ∀ M ≤ U, M ≠ ⊥ →
      (∀ g ∈ Subgroup.normalizer (U : Set H), M.map (MulAut.conj g).toMonoidHom ≤ M) → M = U) :
    Nat.card W ≤ Nat.card U ^ 2 * Nat.card (fixedSpace ρ U) := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hAcard : Nat.card W ≤ measure ρ A := by
    unfold measure
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Nat.card_zmod, hA.card_eq_two_pow_rank, ← pow_mul, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have := fixedCodim_add_finrank ρ A
    omega
  obtain ⟨M, hMU, hmax, hlarge⟩ := exists_largest_maximizer ρ U
  have hbot : measure ρ ⊥ = Nat.card W := by simp [measure, fixedSpace_bot]
  have hMne : M ≠ ⊥ := by
    intro hM
    have he : measure ρ A = measure ρ M :=
      le_antisymm (hmax A hAU) (by rw [hM, hbot]; exact hAcard)
    exact hA.1 (eq_bot_iff.mpr (hM ▸ hlarge A hAU he))
  have hMUeq : M = U := by
    apply hirr M hMU hMne
    intro g hg
    apply hlarge
    · calc
        M.map (MulAut.conj g).toMonoidHom ≤ U.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hMU
        _ = U := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    · exact measure_conj ρ M g
  exact hMUeq ▸ hAcard.trans (hmax A hAU)

end Representation.BinaryOffender
