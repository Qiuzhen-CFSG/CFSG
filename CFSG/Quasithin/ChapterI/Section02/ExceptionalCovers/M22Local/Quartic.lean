module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
public import Theory.Mathieu.M22.CyclicFourCover

/-!
# The Frattini layer of the actual quartic hexad radical

For a cyclic center of order four, the literal hexad radical has order 64.
Its squares lie in the actual central involution subgroup, by passing to
the double cover. Conversely, it contains the center and therefore all
central squares. Thus its Frattini subgroup is exactly the shared central
involution and its Frattini quotient has order 32. In particular the
Frattini subgroup is smaller than the cyclic central subgroup of order four.

These are unconditional steps toward Aschbacher–Smith I.2.2(6), printed
pp.410 and 412 / PDF pp.421 and 423. The A₆ splitting and the equivariant
C₄ ∗ Q₈ ∗ Q₈ recognition remain separate obligations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* M22) [IsCyclic (center K)]
variable (hZ : Nat.card (center K) = 4) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
include hZ hB

omit [Finite K] [IsCyclic (center K)] in
/-- This is the order of the actual full kernel preimage. -/
theorem radical_card : Nat.card (hexadRadical e B) = 64 := by
  rw [hexadRadical_card e hB, hZ]

omit [Finite K] [IsCyclic (center K)] in
/-- The actual radical is a two-group; no abstract order-64 model is used. -/
theorem radical_isPGroup : IsPGroup 2 (hexadRadical e B) :=
  IsPGroup.of_card (n := 6) (radical_card e hZ hB)

/-- Every radical square is in the shared involution of the actual center. -/
theorem radical_square_mem (x : hexadRadical e B) :
    (x : K) ^ 2 ∈ centralSquares K := by
  let := m22HexadPointwiseKernel_elementaryAbelian hB
  exact quartic_square_mem e hZ x
    (elemPow_eq_one_of_isElementaryAbelian (A := m22HexadPointwiseKernel B) _ x.property)

/-- Frattini, mapped into K, is exactly the canonical central involution subgroup. -/
theorem radical_frattini_map :
    (frattini (hexadRadical e B)).map (hexadRadical e B).subtype = centralSquares K :=
  frattini_map_eq_centralSquares _ (radical_isPGroup e hZ hB)
    (center_le_hexadRadical e B) (radical_square_mem e hZ hB)

/-- The same equality in intrinsic radical coordinates. -/
theorem radical_frattini : frattini (hexadRadical e B) =
    (centralSquares K).subgroupOf (hexadRadical e B) := by
  have h := congrArg (Subgroup.comap (hexadRadical e B).subtype)
    (radical_frattini_map e hZ hB)
  simpa only [subgroupOf, comap_map_eq_self_of_injective (hexadRadical e B).subtype_injective] using h

/-- This retains both centrality in K and the shared square-one condition. -/
theorem radical_frattini_mem (x : K) :
    x ∈ (frattini (hexadRadical e B)).map (hexadRadical e B).subtype ↔
      x ∈ center K ∧ x ^ 2 = 1 := by
  rw [radical_frattini_map e hZ hB]
  exact mem_centralSquares_iff hZ x

theorem radical_frattini_card : Nat.card (frattini (hexadRadical e B)) = 2 := by
  rw [← card_map_of_injective (f := (hexadRadical e B).subtype)
    (hexadRadical e B).subtype_injective, radical_frattini_map e hZ hB]
  exact centralSquares_card hZ

/-- The five-dimensional Frattini layer is the one used in binary-cover recognition. -/
theorem radical_frattini_quotient_card :
    Nat.card (hexadRadical e B ⧸ frattini (hexadRadical e B)) = 32 := by
  have h := (frattini (hexadRadical e B)).card_mul_index
  rw [radical_frattini_card e hZ hB, radical_card e hZ hB, index_eq_card] at h
  omega

omit [IsCyclic (center K)] in
theorem radical_frattini_quotient_elementary :
    IsElementaryAbelian 2 (hexadRadical e B ⧸ frattini (hexadRadical e B)) := by
  let : Fact (IsPGroup 2 (hexadRadical e B)) := ⟨radical_isPGroup e hZ hB⟩
  exact isElementaryAbelian_quotient_frattini

/-- The binary radical is literally the quotient of the quartic radical by Frattini. -/
noncomputable def radicalReductionEquiv :
    (hexadRadical e B ⧸ frattini (hexadRadical e B)) ≃*
      hexadRadical (quarticReductionEquiv e) B := by
  let f : hexadRadical e B →* hexadRadical (quarticReductionEquiv e) B :=
    quarticReductionLocal e (m22HexadPointwiseKernel B)
  have hk : frattini (hexadRadical e B) = f.ker :=
    (radical_frattini e hZ hB).trans (quarticReductionLocal_ker e _).symm
  exact (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (quarticReductionLocal_surjective e _))

/-- The equivalence preserves the actual ambient quotient map, not just the group order. -/
@[simp] theorem radicalReductionEquiv_mk (x : hexadRadical e B) :
    (radicalReductionEquiv e hZ hB (QuotientGroup.mk x) : K ⧸ centralSquares K) =
      QuotientGroup.mk' (centralSquares K) (x : K) := rfl

/-- A direct exponent bound in the actual radical. -/
theorem radical_fourth_power (x : hexadRadical e B) : x ^ 4 = 1 := by
  apply Subtype.ext
  change (x : K) ^ 4 = 1
  simpa only [← pow_mul] using centralSquares_square hZ (radical_square_mem e hZ hB x)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
