module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.GroupTheory.IndexNormal

/-!
# The elementary sixteen and Sylow complement in the dimension-four branch

The factor-interchange branch constructs precisely A = ⟨a, [U,a]⟩ as an
actual elementary subgroup of order sixteen. For the complement step we
retain the actual normal V, its PSL₃(2) quotient, a Sylow subgroup TL of L,
and the embedded quaternion core U. These determine |TL| = 64 and |TL:U| = 2.
A complement to V in U normalized by the specified a ∈ Wᵍ − U extends to
an actual complement in TL, of order eight.

The source action dichotomy and construction of that invariant complement
are still separate obligations. In particular this module does not assume
that an elementary sixteen alone supplies the invariant complement, nor
claim the nonsplitting conclusion of 14.4.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. The later global Gaschütz step is outside this module.
-/

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting

variable {L : Type*} [Group L] [Finite L]

/-- The actual natural-block extension has Sylow order sixty-four.
Only the source quotient and the order of its kernel are needed here. -/
public theorem sylow_card_of_block_quotient
    (V : Subgroup L) [V.Normal] (hV : Nat.card V = 8)
    (e : (L ⧸ V) ≃* Matrix.PSL3Two.PSL) (TL : Sylow 2 L) :
    Nat.card TL = 64 := by
  have hq : Nat.card (L ⧸ V) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hL : Nat.card L = 1344 := by
    rw [card_eq_card_quotient_mul_card_subgroup V, hq, hV]
  rw [TL.card_eq_multiplicity, hL]
  decide +kernel

omit [Finite L] in
/-- The marked involution in the genuine elementary Wᵍ constructs the
literal source A, not merely an isomorphic elementary group. -/
public theorem elementary_sixteen_of_marked_swap
    (U W : Subgroup L) (d : QuaternionCentralProductData U)
    [IsElementaryAbelian 2 W] (a : L) (haW : a ∈ W) (haU : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype) :
    ⁅U, zpowers a⁆ = U ⊓ centralizer ({a} : Set L) ∧
    IsElementaryAbelian 2 (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup L) ∧
    Nat.card (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup L) = 16 :=
  d.elementary_sixteen_of_swap U a
    (elemPow_eq_one_of_isElementaryAbelian a haW) haU hswap

/-- The actual normalizer action of the marked involution has the a₂
square-quotient type, and produces the source elementary sixteen. -/
public theorem a2_and_elementary_sixteen_of_marked_swap
    (U W : Subgroup L) (d : QuaternionCentralProductData U)
    [IsElementaryAbelian 2 W] (a : L) (haW : a ∈ W) (haU : a ∉ U)
    (haN : a ∈ normalizer (U : Set L))
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype) :
    d.IsA2Action (U.normalizerMonoidHom ⟨a, haN⟩) ∧
    ⁅U, zpowers a⁆ = U ⊓ centralizer ({a} : Set L) ∧
    IsElementaryAbelian 2 (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup L) ∧
    Nat.card (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup L) = 16 := by
  have ha : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haW
  let α := U.normalizerMonoidHom ⟨a, haN⟩
  have hα : α ^ 2 = 1 := by
    have hp : (⟨a, haN⟩ : normalizer (U : Set L)) ^ 2 = 1 := Subtype.ext ha
    dsimp [α]
    rw [← map_pow, hp, map_one]
  have hs : d.left.map α.toMonoidHom = d.right := by
    apply map_injective U.subtype_injective
    rw [map_map]
    have he : U.subtype.comp α.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp U.subtype := rfl
    rw [he, ← map_map]
    exact hswap
  exact ⟨d.isA2Action_of_swap α hα hs,
    elementary_sixteen_of_marked_swap U W d a haW haU hswap⟩

/-- Extend the constructed invariant complement to the actual Sylow subgroup.
Its order and generation are derived from the literal PSL₃(2) quotient;
no Sylow-order or generation assertion is an extra premise. -/
public theorem sylow_complement_of_invariant_core_complement
    (V : Subgroup L) [V.Normal] (hV : Nat.card V = 8)
    (e : (L ⧸ V) ≃* Matrix.PSL3Two.PSL) (TL : Sylow 2 L)
    (U D W : Subgroup TL) (d : QuaternionCentralProductData U)
    [IsElementaryAbelian 2 W] (a : TL) (haW : a ∈ W) (haU : a ∉ U)
    (hDU : D ≤ U) (hspan : V.subgroupOf (TL : Subgroup L) ⊔ D = U)
    (hdisj : Disjoint (V.subgroupOf (TL : Subgroup L)) D)
    (hinvariant : a ∈ normalizer (D : Set TL)) :
    (V.subgroupOf (TL : Subgroup L)).IsComplement' (D ⊔ zpowers a) ∧
    Nat.card (D ⊔ zpowers a : Subgroup TL) = 8 := by
  have hTL := sylow_card_of_block_quotient V hV e TL
  have hindex : U.index = 2 := by
    have hc := U.card_mul_index
    rw [d.card, hTL] at hc
    omega
  let : U.Normal := U.normal_of_index_eq_two hindex
  have ha : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haW
  have hgen : U ⊔ zpowers a = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top, hTL,
      card_sup_zpowers_of_normalizing_involution U a ha haU
        (by rw [U.normalizer_eq_top]; trivial), d.card]
  have hcomp := isComplement_sup_zpowers_of_invariant U
    (V.subgroupOf (TL : Subgroup L)) D hDU hspan hdisj a ha haU hinvariant hgen
  have hVTL : V ≤ (TL : Subgroup L) := by
    exact (IsPGroup.of_card (p := 2) (n := 3) hV).le_sylow_of_normal TL
  have hV0 : Nat.card (V.subgroupOf (TL : Subgroup L)) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVTL).toEquiv).trans hV
  refine ⟨hcomp, ?_⟩
  have hc := hcomp.card_mul_card
  rw [hV0, hTL] at hc
  omega

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting
