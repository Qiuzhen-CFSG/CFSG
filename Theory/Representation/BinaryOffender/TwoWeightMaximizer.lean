module

public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
public import Theory.Representation.GeneratedSubgroupInvariants
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness

/-!
# Exponent-two offender maximization

Maximize `|B|² |C_V(B)|` among subgroups of a specified subgroup U, then
choose a maximizer of largest order. The subgroup-index inequality and the
fixed-space intersection inequality show that joins of maximizers remain
maximizers. Thus the largest maximizer is normalized by the actual normalizer
of U. A nontrivial elementary actor of fixed codimension at most twice its
rank ensures that this maximizer is nontrivial and remains an offender.

The final estimates turn its order and actual conjugate generation into a
bound on the whole module. Neither cubicity nor irreducibility is used in
maximization; the conjugate estimate retains the zero fixed-space hypothesis.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Lemma 2.1,
author manuscript pp.5--6, and Proposition 6.2, pp.38--39. The exponent-one
argument in `QuasisimpleCardBound/Maximizer.lean` supplies the proof pattern
for the index inequality; it is not used as an exponent-two theorem.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender.TwoWeight
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The exact exponent-two measure from GM04, for an arbitrary subgroup. -/
noncomputable def measure (B : Subgroup G) : ℕ :=
  Nat.card B ^ 2 * Nat.card (fixedSpace ρ B)

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

/-- The group-order and fixed-space inequalities multiply to supermodularity. -/
theorem measure_supermodular (B C : Subgroup G) :
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
/-- Conjugation preserves both factors in the measure. -/
theorem measure_conj (B : Subgroup G) (g : G) :
    measure ρ (B.map (MulAut.conj g).toMonoidHom) = measure ρ B := by
  unfold measure
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    ← Nat.card_congr (fixedSpaceConjEquiv ρ B g).toEquiv]

/-- The unique largest maximizer among all subgroups of the specified U. -/
theorem exists_largest_maximizer (U : Subgroup G) :
    ∃ B ≤ U, (∀ C ≤ U, measure ρ C ≤ measure ρ B) ∧
      (∀ C ≤ U, measure ρ C = measure ρ B → C ≤ B) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨D, hDU, hD⟩ := Set.exists_max_image {C : Subgroup G | C ≤ U}
    (measure ρ) (Set.toFinite _) ⟨⊥, show (⊥ : Subgroup G) ≤ U from bot_le⟩
  let S : Set (Subgroup G) := {C | C ≤ U ∧ measure ρ C = measure ρ D}
  obtain ⟨B, hB, hcard⟩ := Set.exists_max_image S (fun C => Nat.card C)
    (Set.toFinite _) ⟨D, hDU, rfl⟩
  have hmax (C : Subgroup G) (hC : C ≤ U) : measure ρ C ≤ measure ρ B := by
    rw [show measure ρ B = measure ρ D from hB.2]
    exact hD C hC
  refine ⟨B, hB.1, hmax, ?_⟩
  intro C hCU hC
  have hpos : 0 < measure ρ B := Nat.mul_pos (pow_pos Nat.card_pos _) Nat.card_pos
  have hjoin : measure ρ (B ⊔ C) = measure ρ B := by
    apply le_antisymm (hmax _ (sup_le hB.1 hCU))
    have hi := measure_supermodular ρ B C
    rw [hC] at hi
    have hu := Nat.mul_le_mul_right (measure ρ (B ⊔ C))
      (hmax (B ⊓ C) (inf_le_left.trans hB.1))
    exact Nat.le_of_mul_le_mul_left (hi.trans hu) hpos
  have he : B = B ⊔ C := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hcard (B ⊔ C) ⟨sup_le hB.1 hCU, hjoin.trans hB.2⟩)
  exact he ▸ le_sup_right

/-- Translate the binary actor inequality into the source cardinality measure. -/
theorem card_le_measure_of_small_codim {A : Subgroup G} (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρ A ≤ 2 * rank A) : Nat.card V ≤ measure ρ A := by
  have hd := fixedCodim_add_finrank ρ A
  unfold measure
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
    Nat.card_zmod, hA.card_eq_two_pow_rank, ← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Replace an offender inside U by a nontrivial offender normalized by N(U).
The resulting subgroup need not remain cubic or contain the original actor. -/
theorem exists_normalized_offender (U : Subgroup G) {A : Subgroup G}
    (hAU : A ≤ U) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ B ≤ U, B ≠ ⊥ ∧ normalizer (U : Set G) ≤ normalizer (B : Set G) ∧
      Nat.card V ≤ measure ρ B := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨B, hBU, hmax, hlarge⟩ := exists_largest_maximizer ρ U
  have hcard := card_le_measure_of_small_codim ρ hA hcodim
  have hnon : B ≠ ⊥ := by
    intro hbot
    have he : measure ρ A = measure ρ B := le_antisymm (hmax A hAU) (by
      simpa [hbot, measure, fixedSpace_bot] using hcard)
    exact hA.1 (eq_bot_iff.mpr (hbot ▸ hlarge A hAU he))
  refine ⟨B, hBU, hnon, ?_, hcard.trans (hmax A hAU)⟩
  intro g hg
  have hmap (g : G) (hg : g ∈ normalizer (U : Set G)) :
      B.map (MulAut.conj g).toMonoidHom ≤ B := by
    apply hlarge _ ?_ (measure_conj ρ B g)
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg b).mp (hBU hb)
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hmap g hg (Subgroup.mem_map_of_mem _ hb)
  · intro hb
    have hh := hmap g⁻¹ ((normalizer (U : Set G)).inv_mem hg)
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb)
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using hh

omit [Finite G] in
/-- An offender of order at most 2^s has fixed codimension at most 2s. -/
theorem fixedCodim_le_of_card_le_measure {B : Subgroup G} {s : ℕ}
    (hV : Nat.card V ≤ measure ρ B) (hB : Nat.card B ≤ 2 ^ s) :
    fixedCodim ρ B ≤ 2 * s := by
  have hd := fixedCodim_add_finrank ρ B
  have hb := Nat.mul_le_mul_right (Nat.card (fixedSpace ρ B))
    (Nat.pow_le_pow_left hB 2)
  have hh := hV.trans hb
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ B),
    Nat.card_zmod, ← pow_mul, ← pow_add] at hh
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  omega

omit [Finite G] in
/-- Actual generation by n conjugates bounds the whole degree by 2ns. -/
theorem finrank_le_of_conjugates {B : Subgroup G} {n s : ℕ}
    (hfix : fixedSpace ρ ⊤ = ⊥)
    (hV : Nat.card V ≤ measure ρ B) (hB : Nat.card B ≤ 2 ^ s)
    (g : Fin n → G) (hgen : (⨆ i, B.map (MulAut.conj (g i)).toMonoidHom) = ⊤) :
    Module.finrank (ZMod 2) V ≤ n * (2 * s) := by
  have hd := finrank_le_card_mul_fixedCodim_of_subgroup_conjugates
    ρ ⊤ B hfix g hgen.ge
  simp only [Fintype.card_fin] at hd
  exact hd.trans (Nat.mul_le_mul_left n (fixedCodim_le_of_card_le_measure ρ hV hB))

end Representation.BinaryOffender.TwoWeight
