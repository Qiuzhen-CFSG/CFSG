module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter5.RankOneBaumannSource
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer

/-!
# The original rank-one input and its commutator module

Convert the original maximal local family and reduced subgroup into the
intrinsic Chapter 1 and reduced-module interfaces. The actual PSL2 quotient
is centerless and quasisimple. Its Sylow supplement makes L the two-residual,
so [W,L] remains reduced and again satisfies every original input hypothesis.
No chosen-module invariance or excluded ambient model is assumed.

Source: Aschbacher--Smith 5.0.1,5.1.1 and the replacement of V by [V,L]
in 5.1.7(1), printed pp.629--630,633.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

theorem Input.maximal_local
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    L ∈ Chapter1.LStar G (T : Subgroup G) := by
  refine ⟨h.local_mem.1.prop, ?_⟩
  intro K hK hLK
  exact le_antisymm (h.local_mem.1.2 hK hLK) hLK

theorem Input.reduced_internal
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    IsPReduced 2 (W.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := h.reduced.2.1
  exact ⟨h.reduced.2.2.choose,
    IsElementaryAbelian.of_injective
      (subgroupOfEquivOfLe h.reduced.1).toMonoidHom
      (subgroupOfEquivOfLe h.reduced.1).injective,
    h.reduced.2.2.choose_spec⟩

theorem Input.quotient_center_eq_bot
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp
    (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot.le ((centerCongr e) ⟨x,hx⟩).property)

theorem Input.quotient_quasisimple
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_local.1
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  refine ⟨?_⟩
  apply (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq h.quotient_center_eq_bot).trans
      QuotientGroup.quotientBot)).mpr
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.linear
  apply (MulEquiv.isSimpleGroup_congr e).mpr
  apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  rw [hF]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) h.exponent).trans' (by decide)

theorem Input.commutator_reduced
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ⁅W,L⁆ ∈ reducedFamily (L ⊔ (T : Subgroup G)) := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let U := W.subgroupOf J
  have hr : IsPReduced 2 U := h.reduced_internal
  let : U.Normal := hr.normal
  let : IsElementaryAbelian 2 U := hr.elementary
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  have hp : IsPPerfect 2 K := h.local_mem.2.2.1.of_surjective
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.surjective
  have hres : pResidual 2 J = K := by
    apply pResidual_eq_of_isPPerfect_sup K ((T : Subgroup G).subgroupOf J)
      hp T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right, subgroupOf_self]
  have hm : IsPReduced 2 ⁅U,K⁆ := by
    rw [← hres]
    exact hr.moved U
  have he : (⁅U,K⁆).map J.subtype = ⁅W,L⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le h.reduced.1,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
  have hle : ⁅W,L⁆ ≤ J := he ▸ map_subtype_le _
  have hi : (⁅W,L⁆).subgroupOf J = ⁅U,K⁆ := by
    rw [← he]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hm' : IsPReduced 2 ((⁅W,L⁆).subgroupOf J) := hi.symm ▸ hm
  refine ⟨hle, ?_, hm'.normal, hm'.quotient_pCore_eq_bot⟩
  let := hm.elementary
  rw [← he]
  exact IsElementaryAbelian.map _

theorem Input.commutator_input
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    Input KnownSimple.IsKnownSimple T L ⁅W,L⁆ n := by
  refine { h with reduced := h.commutator_reduced, noncentral := ?_ }
  let := Chapter1.mem_L_isPerfect h.maximal_local.1
  exact fun he => h.noncentral (commutator_eq_bot_of_iterated_eq_bot W L he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
