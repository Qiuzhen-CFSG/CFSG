module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTriality
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.Representation.SL2.MovedElementaryDegree
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The original moved module bounds the marked triality degree

The nonzero commutator of the chosen reduced subgroup with L is elementary,
normal in the original Sylow, and contained in T ∩ L. Its noncentral
PSL₂ constituent gives size at least 2^(2n). In a marked binary-triality
right parabolic, the same subgroup embeds in the genuine carrier of
two-rank five. Hence 2n ≤ 5, and the original n > 1 forces n = 2.

This proof does not equate the original left degree with the right quotient
degree three, nor does it need S = T. The normality and size bounds also
feed the actual Hall–Janko exclusions in ZeroCoreJanko.
Source: Aschbacher–Smith 5.2.2, printed pp.647–648; the constituent bound
is E.2.13(4), p.225, and the triality rank is the genuine root calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original moved reduced subgroup lies in the left Sylow intersection
and has at least the binary dimension of a noncentral PSL₂ constituent. -/
theorem Input.moved_reduced_size {κ : GroupClass}
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) :
    IsElementaryAbelian 2 (⁅W,L⁆ : Subgroup G) ∧ ⁅W,L⁆ ≤ (T : Subgroup G) ⊓ L ∧
      2 ^ (2 * n) ≤ Nat.card (⁅W,L⁆ : Subgroup G) := by
  have hLN : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer h.sylow_normalizes
  have hWN : L ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.reduced.1).mp h.reduced.2.2.choose
  have hLW := (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans hWN
  have hUL : ⁅W,L⁆ ≤ L := le_normalizer_iff_commutator_le_right.mp (h.reduced.1.trans hLN)
  have hUW : ⁅W,L⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
  let : IsElementaryAbelian 2 W := h.reduced.2.1
  let : IsElementaryAbelian 2 (⁅W,L⁆ : Subgroup G) := IsElementaryAbelian.of_le hUW
  have hUcore : ⁅W,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (⁅W,L⁆ : Subgroup G)) hUL (normalizer_commutator_ge_right W L)
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))
      (hLN.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    exact hc.trans ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have hm : ⁅⁅W,L⁆,L⁆ = ⁅W,L⁆ := commutator_isPPerfect_idempotent L W
    h.local_mem.2.2.1 (IsElementaryAbelian.isPGroup 2 W) hLW
  let := h.local_mem.1.1.1.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨inferInstance,le_inf (hUcore.trans hcoreT) hUL,
    Representation.SL2.moved_subgroup_card_bound L ⁅W,L⁆ hUL h.noncentral hm
      (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm) (by have := h.exponent; omega) hF⟩

/-- The moved subgroup of the original reduced module is normal in the
original Sylow; this uses both literal normalization relations. -/
theorem Input.moved_reduced_normalizes {κ : GroupClass}
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) :
    (T : Subgroup G) ≤ normalizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
  have hWN : L ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.reduced.1).mp h.reduced.2.2.choose
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hWN (mem_sup_right ht)),
    mem_normalizer_iff_map_conj_eq.mp (h.sylow_normalizes ht)]

namespace Prime
open Triality.Standard Triality.Standard.Parabolics
/-- The marked binary-triality endpoint forces the original left degree to two.
This compares the original moved module with the actual model's two-rank;
it does not identify the left degree with the right quotient degree three. -/
theorem LocalData.binaryTriality_original_degree
    {T : Sylow 2 G} {L W H B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (e : (R ⊔ Global.sourceS L H : Subgroup G) ≃*
      parabolic (binaryParameters 1 Nat.zero_lt_one) .arms) : n = 2 := by
  obtain ⟨he,hUT,hlow⟩ := h.moved_reduced_size
  let := he
  let U := ⁅W,L⁆
  have hUS : U ≤ Global.sourceS L H := by
    rw [←d.S_intersection_left] at hUT
    exact hUT.trans inf_le_left
  let P := binaryParameters 1 Nat.zero_lt_one
  let J := R ⊔ Global.sourceS L H
  let f : U →* Carrier P := (parabolic P .arms).subtype.comp
    (e.toMonoidHom.comp (inclusion (hUS.trans (show Global.sourceS L H ≤ J from le_sup_right))))
  have hf : Function.Injective f := (parabolic P .arms).subtype_injective.comp
    (e.injective.comp (inclusion_injective _))
  let : IsElementaryAbelian 2 (⊤ : Subgroup U) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup U).subtype Subtype.val_injective
  let E := (⊤ : Subgroup U).map f
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hupper := (primeRank_le_iff_elementary_card_le (Carrier P)).mp
    (TwoRank.twoRank_le_five_mul 1 Nat.zero_lt_one) E hE
  rw [card_map_of_injective hf,card_top] at hupper
  have hn : 2 * n ≤ 5 * 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hlow.trans hupper)
  have := h.exponent
  omega
end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
