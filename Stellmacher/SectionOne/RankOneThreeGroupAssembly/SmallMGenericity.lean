module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.ExceptionalFactor

/-!
# Small action ratios exclude exceptional local factors

If an elementary abelian actor `S` satisfies `m(S) < 2`, every displayed
local order-three factor in the recursive construction is generic. Otherwise
the failed factor has an ambient commutator module of order sixteen and its
intersection with `C_V(A)` has order four, for an order-two `A ∈ oneAmax S`.
Relative-index monotonicity gives `|V:C_V(A)| ≥ 4`, hence `m(A) ≥ 2`, contrary
to `m(A) ≤ m(S)`.

This proves the local-factor assertion needed by the restricted form of
Stellmacher (1.6) used in (1.7). The proof is independent of the unrestricted
exceptional branch's claimed equality for `m(S)`.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal p. 18.
-/

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u

private theorem m_ge_two_of_card_sixteen_fixed_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (A : Subgroup G) (U : Subgroup V)
    (hAcard : Nat.card A = 2) (hUcard : Nat.card U = 16)
    (hfixed : Nat.card (U ⊓ FixedPoints.subgroup A V : Subgroup V) = 4) :
    2 ≤ m (G := G) (V := V) A := by
  let C : Subgroup V := FixedPoints.subgroup A V
  have hrel : Nat.card (U ⊓ C : Subgroup V) * C.relIndex U = Nat.card U := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) (U ⊓ C) U bot_le inf_le_left
  have hrelFour : C.relIndex U = 4 := by
    change Nat.card (U ⊓ FixedPoints.subgroup A V : Subgroup V) * C.relIndex U = Nat.card U at hrel
    rw [hfixed, hUcard] at hrel
    omega
  have hidx : 4 ≤ C.index := by
    have hmono : C.relIndex U ≤ C.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right (show U ≤ ⊤ from le_top)
        (Nat.card_pos (α := (⊤ : Subgroup V) ⧸ C.subgroupOf ⊤)).ne'
    simpa [hrelFour] using hmono
  have hcard : 4 * Nat.card C ≤ Nat.card V := by
    calc
      4 * Nat.card C ≤ C.index * Nat.card C := Nat.mul_le_mul_right _ hidx
      _ = Nat.card V := C.index_mul_card
  have hCpos : (0 : ℚ) < Nat.card C := by exact_mod_cast Nat.card_pos (α := C)
  unfold m
  rw [hAcard]
  change 2 ≤ (Nat.card V : ℚ) / ((Nat.card C : ℚ) * 2)
  apply (le_div_iff₀ (mul_pos hCpos (by norm_num))).mpr
  have hcardQ : (4 : ℚ) * Nat.card C ≤ Nat.card V := by exact_mod_cast hcard
  nlinarith

public theorem generic_of_m_lt_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hm : m (G := G) (V := V) S < 2) :
    RankOneAssemblyGenericHypothesis (G := G) (V := V) S := by
  by_contra hnongeneric
  obtain ⟨A, F, hAmax, hAcard, _, _, _, _, hfixed, hUcard⟩ :=
    exists_exceptional_local_factor_fixed_card_data S hS hnongeneric
  have htwo : 2 ≤ m (G := G) (V := V) A :=
    m_ge_two_of_card_sixteen_fixed_card_four A (commutatorAction F V)
      hAcard hUcard hfixed
  exact (not_lt_of_ge (htwo.trans hAmax.2.1)) hm

end Stellmacher.SectionOne.RankOneThreeGroupAssembly

