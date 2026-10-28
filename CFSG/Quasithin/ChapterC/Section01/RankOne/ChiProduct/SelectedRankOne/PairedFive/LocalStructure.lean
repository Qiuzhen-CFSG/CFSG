module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Baumann
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.FactorMarking
public import Theory.Representation.NormalElementaryQuotient
/-!
# The original component-normalizer join and its moved module

The selected component and its original Sylow normalizer normalize the
literal commutator [U,L]. Restriction to their join therefore gives a normal
elementary subgroup with the same binary coordinates. These definitions
preserve the ambient inclusions used in C.1.23.

Source: Aschbacher–Smith C.1.26, printed p.132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
variable {G : Type*} [Group G]

abbrev localJoin (T L : Subgroup G) : Subgroup G := L ⊔ (T ⊓ normalizer (L : Set G))
abbrev localMoved (T U L : Subgroup G) : Subgroup (localJoin T L) := (⁅U,L⁆).subgroupOf (localJoin T L)

instance localComponent_normal (T L : Subgroup G) : (L.subgroupOf (localJoin T L)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)

theorem localJoin_normalizes_moved (T U L : Subgroup G) [U.Normal] :
    localJoin T L ≤ normalizer ((⁅U,L⁆ : Subgroup G) : Set G) := by
  apply sup_le (normalizer_commutator_ge_right U L)
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅U,L⁆ : Subgroup G).map (MulAut.conj b).toMonoidHom = ⁅U,L⁆
  have hl : L.map (MulAut.conj b).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hb.2
  have hu : U.map (MulAut.conj b).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (U.normalizer_eq_top.symm ▸ mem_top b)
  rw [map_commutator,hl,hu]

instance localMoved_normal (T U L : Subgroup G) [U.Normal] : (localMoved T U L).Normal :=
  normal_subgroupOf_of_le_normalizer (localJoin_normalizes_moved T U L)

instance localMoved_elementary (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] :
    IsElementaryAbelian 2 (localMoved T U L) := by
  let : IsElementaryAbelian 2 (⁅U,L⁆ : Subgroup G) := IsElementaryAbelian.of_le (commutator_le_left U L)
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (A := (⁅U,L⁆ : Subgroup G)) ((x : localJoin T L) : G) x.property

@[expose] noncomputable def movedEquiv (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUL : U ≤ normalizer (L : Set G)) :
    letI : IsElementaryAbelian 2 (⁅U,L⁆ : Subgroup G) := IsElementaryAbelian.of_le (commutator_le_left U L)
    Additive (localMoved T U L) ≃ₗ[ZMod 2] Additive (⁅U,L⁆ : Subgroup G) := by
  let : IsElementaryAbelian 2 (⁅U,L⁆ : Subgroup G) := IsElementaryAbelian.of_le (commutator_le_left U L)
  let e := subgroupOfEquivOfLe ((le_normalizer_iff_commutator_le_right.mp hUL).trans
    (show L ≤ localJoin T L from le_sup_left))
  exact LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
