module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Minimal action ratios and the action kernel

For a subgroup `K ≤ S`, the inequality `m(S) ≤ m(K)` bounds the quotient
`C_V(K)/C_V(S)` by the index `[S:K]`. If a subgroup `U ≤ C_V(K)` has a
larger quotient by `U ∩ C_V(S)`, then `K` must be trivial. The proof uses
relative-index monotonicity to compare these quotients and clears the positive
cardinality denominators in the definition of `m`.

The second theorem specializes this argument to an action module of order
sixteen with two common fixed points and an action image of order four.
This is the kernel-elimination step in Stellmacher (1.6), journal page 18,
`refs/latex/stellmacher-n-group.tex`. It does not assert the later exceptional
classification or any value for `m(S)`.
-/

open scoped Pointwise

namespace Stellmacher.SectionOne

universe u v

private theorem subgroup_card_product_le
    {V : Type v} [Group V] [Finite V]
    (U C K : Subgroup V) (hUK : U ≤ K) (hCK : C ≤ K) :
    Nat.card U * Nat.card C ≤ Nat.card (U ⊓ C : Subgroup V) * Nat.card K := by
  have hU : Nat.card (U ⊓ C : Subgroup V) * C.relIndex U = Nat.card U := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) (U ⊓ C) U bot_le inf_le_left
  have hK : Nat.card C * C.relIndex K = Nat.card K := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup V) C K bot_le hCK
  have hindex : C.relIndex U ≤ C.relIndex K :=
    Subgroup.relIndex_le_of_le_right hUK (Nat.card_pos (α := K ⧸ C.subgroupOf K)).ne'
  calc
    Nat.card U * Nat.card C =
        Nat.card (U ⊓ C : Subgroup V) * (Nat.card C * C.relIndex U) := by
      rw [← hU]
      ac_rfl
    _ ≤ Nat.card (U ⊓ C : Subgroup V) * (Nat.card C * C.relIndex K) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hindex)
    _ = Nat.card (U ⊓ C : Subgroup V) * Nat.card K := by rw [hK]

public theorem minimal_m_action_kernel_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S K : Subgroup G) (U : Subgroup V)
    (hKS : K ≤ S)
    (hfix : U ≤ FixedPoints.subgroup K V)
    (hmin : K ≠ ⊥ → m (G := G) (V := V) S ≤ m (G := G) (V := V) K)
    (hlarge : Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) * Nat.card S <
      Nat.card U * Nat.card K) :
    K = ⊥ := by
  by_contra hK
  have hCSCK : FixedPoints.subgroup S V ≤ FixedPoints.subgroup K V := by
    intro z hz
    rw [FixedPoints.mem_subgroup] at hz ⊢
    intro k
    exact hz ⟨k, hKS k.property⟩
  have hprod := subgroup_card_product_le U (FixedPoints.subgroup S V)
    (FixedPoints.subgroup K V) hfix hCSCK
  have hm := hmin hK
  have hVpos : (0 : ℚ) < Nat.card V := by exact_mod_cast Nat.card_pos (α := V)
  have hCSpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup S V) := by
    exact_mod_cast Nat.card_pos (α := FixedPoints.subgroup S V)
  have hCKpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup K V) := by
    exact_mod_cast Nat.card_pos (α := FixedPoints.subgroup K V)
  have hSpos : (0 : ℚ) < Nat.card S := by exact_mod_cast Nat.card_pos (α := S)
  have hKpos : (0 : ℚ) < Nat.card K := by exact_mod_cast Nat.card_pos (α := K)
  have hcard : Nat.card (FixedPoints.subgroup K V) * Nat.card K ≤
      Nat.card (FixedPoints.subgroup S V) * Nat.card S := by
    unfold m at hm
    have hden := (div_le_div_iff₀ (mul_pos hCSpos hSpos) (mul_pos hCKpos hKpos)).mp hm
    have hden' : (Nat.card (FixedPoints.subgroup K V) : ℚ) * Nat.card K ≤
        (Nat.card (FixedPoints.subgroup S V) : ℚ) * Nat.card S := by
      nlinarith
    exact_mod_cast hden'
  have hbound : Nat.card U * Nat.card K ≤
      Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) * Nat.card S := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card (FixedPoints.subgroup S V))
    calc
      Nat.card U * Nat.card K * Nat.card (FixedPoints.subgroup S V) =
          (Nat.card U * Nat.card (FixedPoints.subgroup S V)) * Nat.card K := by ac_rfl
      _ ≤ (Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) *
          Nat.card (FixedPoints.subgroup K V)) * Nat.card K :=
        Nat.mul_le_mul_right _ hprod
      _ = Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) *
          (Nat.card (FixedPoints.subgroup K V) * Nat.card K) := by ac_rfl
      _ ≤ Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) *
          (Nat.card (FixedPoints.subgroup S V) * Nat.card S) := Nat.mul_le_mul_left _ hcard
      _ = (Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) * Nat.card S) *
          Nat.card (FixedPoints.subgroup S V) := by ac_rfl
    exact Nat.card_pos
  exact (not_lt_of_ge hbound) hlarge

public theorem exceptional_minimal_m_kernel_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G) (U : Subgroup V)
    (hmin : ∀ K : Subgroup G, K ≤ S → K ≠ ⊥ →
      m (G := G) (V := V) S ≤ m (G := G) (V := V) K)
    (hUcard : Nat.card U = 16)
    (hfixed : Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) = 2)
    (hindex : Nat.card S = 4 * Nat.card (S ⊓ fixingSubgroup G (U : Set V) : Subgroup G)) :
    S ⊓ fixingSubgroup G (U : Set V) = ⊥ ∧ Nat.card S = 4 := by
  let K : Subgroup G := S ⊓ fixingSubgroup G (U : Set V)
  have hKS : K ≤ S := inf_le_left
  have hfix : U ≤ FixedPoints.subgroup K V := by
    intro z hz
    rw [FixedPoints.mem_subgroup]
    intro k
    exact (mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp k.property.2 z hz
  have hlarge : Nat.card (U ⊓ FixedPoints.subgroup S V : Subgroup V) * Nat.card S <
      Nat.card U * Nat.card K := by
    rw [hUcard, hfixed, hindex]
    change 2 * (4 * Nat.card K) < 16 * Nat.card K
    have hKpos : 0 < Nat.card K := Nat.card_pos
    omega
  have hK : K = ⊥ := minimal_m_action_kernel_eq_bot S K U hKS hfix (hmin K hKS) hlarge
  refine ⟨hK, ?_⟩
  change Nat.card S = 4 * Nat.card K at hindex
  simpa [hK] using hindex

end Stellmacher.SectionOne

