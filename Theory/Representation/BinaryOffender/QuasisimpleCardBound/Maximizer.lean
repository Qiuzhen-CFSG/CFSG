module

public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.NormalInvariants
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness

/-!
# The exponent-one offender cardinality bound

For an arbitrary subgroup B, maximize |B| |C_V(B)|, then choose a maximizer
of largest order. The subgroup index inequality and the fixed-space dimension
formula show that joins of maximizers are maximizers. Thus the largest one
contains every maximizer and is normal. An offender ensures it is nontrivial;
faithfulness and irreducibility make its fixed space zero. Consequently
|V| is at most the order of the acting group.

This is the exponent-one adaptation of Guralnick--Malle,
*Classification of 2F-modules, I*, Section 2, Lemma 2.1 (printed p.3).
Their displayed measure has exponent two; the exponent-one result needed
for binary FF-modules is proved here independently from the same inequalities.
-/

public section
open Representation Representation.BinaryOffender Subgroup

namespace Representation.BinaryOffender.QuasisimpleCardBound
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private noncomputable def measure (B : Subgroup G) : ℕ := Nat.card B * Nat.card (fixedSpace ρ B)

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
  have hh := Nat.mul_le_mul (group_card_inequality B C) hf
  dsimp [measure]
  convert hh using 1 <;> ring

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem measure_conj (B : Subgroup G) (g : G) :
    measure ρ (B.map (MulAut.conj g).toMonoidHom) = measure ρ B := by
  unfold measure
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    ← Nat.card_congr (fixedSpaceConjEquiv ρ B g).toEquiv]

private theorem exists_largest_maximizer :
    ∃ K : Subgroup G, (∀ B, measure ρ B ≤ measure ρ K) ∧
      (∀ B, measure ρ B = measure ρ K → B ≤ K) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨D, _, hD⟩ := Set.exists_max_image (Set.univ : Set (Subgroup G))
    (measure ρ) (Set.toFinite _) Set.univ_nonempty
  let S : Set (Subgroup G) := {B | measure ρ B = measure ρ D}
  obtain ⟨K, hK, hcard⟩ := Set.exists_max_image S (fun B => Nat.card B)
    (Set.toFinite _) ⟨D, rfl⟩
  have hmax (B : Subgroup G) : measure ρ B ≤ measure ρ K := by
    rw [show measure ρ K = measure ρ D from hK]
    exact hD B (Set.mem_univ B)
  refine ⟨K, hmax, ?_⟩
  intro B hB
  have hpos : 0 < measure ρ K := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hjoin : measure ρ (K ⊔ B) = measure ρ K := by
    apply le_antisymm (hmax _)
    have hi := measure_supermodular ρ K B
    rw [hB] at hi
    have hu := Nat.mul_le_mul_right (measure ρ (K ⊔ B)) (hmax (K ⊓ B))
    exact Nat.le_of_mul_le_mul_left (hi.trans hu) hpos
  have he : K = K ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hcard (K ⊔ B) (hjoin.trans hK))
  exact he ▸ le_sup_right

/-- Exponent-one maximization bounds a faithful irreducible FF-module by its group. -/
theorem card_le_group_of_offender [IsIrreducible ρ] (hρ : Function.Injective ρ)
    {A : Subgroup G} (hA : IsOffender ρ A) : Nat.card V ≤ Nat.card G := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hAcard : Nat.card V ≤ measure ρ A := by
    unfold measure
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Nat.card_zmod, hA.1.card_eq_two_pow_rank, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) ((fixedCodim_le_rank_iff ρ A).mp hA.2)
  obtain ⟨K, hmax, hlarge⟩ := exists_largest_maximizer ρ
  have hbot : measure ρ ⊥ = Nat.card V := by
    simp [measure, fixedSpace_bot]
  have hKne : K ≠ ⊥ := by
    intro hK
    have he : measure ρ A = measure ρ K :=
      le_antisymm (hmax A) (by rw [hK, hbot]; exact hAcard)
    exact hA.1.1 (eq_bot_iff.mpr (hK ▸ hlarge A he))
  let : K.Normal := ⟨fun n hn g =>
    hlarge (K.map (MulAut.conj g).toMonoidHom) (measure_conj ρ K g)
      (Subgroup.mem_map_of_mem _ hn)⟩
  have hfixed : fixedSpace ρ K = ⊥ := by
    by_contra h
    have hk := ρ.le_ker_of_normal_invariants_ne_bot K h
    apply hKne
    apply eq_bot_iff.mpr
    intro x hx
    exact Subgroup.mem_bot.mpr (hρ ((MonoidHom.mem_ker.mp (hk hx)).trans (map_one ρ).symm))
  calc
    Nat.card V ≤ measure ρ K := hbot ▸ hmax ⊥
    _ = Nat.card K := by simp [measure, hfixed]
    _ ≤ Nat.card G := Nat.card_le_card_of_injective _ Subtype.val_injective

end Representation.BinaryOffender.QuasisimpleCardBound
