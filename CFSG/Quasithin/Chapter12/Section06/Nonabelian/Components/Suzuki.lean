module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.ActionTransport
public import Theory.SpecificGroups.Suzuki.InvolutorySplitTorus
public import Theory.Quasithin.CoprimeRank

/-!
# Suzuki witnesses in the selected component's literal action

The original H-to-H/O₂(H) map preserves the selected K's three-rank.
If K-star is marked as a Suzuki group, a nontrivial element of the actual
V action inverts an element of K-star of odd order greater than five.
The witness retains its membership in both original star images and its
literal conjugation equation in H/O₂(H).

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent
variable {G : Type*} [Group G] [Finite G] {E : Setup G} {H : Subgroup G}
  (c : E.SelectedComponent H)

/-- The original selected K and its image modulo O₂(H) have the same three-rank. -/
theorem three_rank_eq_star : primeRank 3 c.K = primeRank 3 (star H c.K) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.subgroupMap (c.K.subgroupOf H)
  have hker : f.ker = (pCore 2 H).comap (c.K.subgroupOf H).subtype := by
    ext k
    constructor
    · intro hk
      exact (QuotientGroup.eq_one_iff k.val).mp (congrArg Subtype.val hk)
    · intro hk
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff k.val).mpr hk
  have hp : IsPGroup 2 f.ker := hker.symm ▸ pCore_isPGroup.comap_subtype
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (primeRank_congr 3 (subgroupOfEquivOfLe c.le_H)).symm.trans
    (primeRank_eq_of_surjective_of_coprime 3 f (q.subgroupMap_surjective _) hc)
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent

namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
variable {G : Type*} [Group G] [Finite G] {E : Setup G} {H : Subgroup G}
  {c : E.SelectedComponent H} (a : c.ActionMarking)

omit [Finite G] in
include a in
/-- A Suzuki marking produces a forbidden odd-order witness for the original V action. -/
theorem suzuki_inverted_witness (m : ℕ) (hm : 0 < m)
    (e : (star H c.K) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ∃ t ∈ star H E.V, ∃ x ∈ star H c.K,
      Odd (orderOf x) ∧ 5 < orderOf x ∧ t*x*t⁻¹ = x⁻¹ := by
  let B := star H c.K
  let e' := e
  let U := (E.V.subgroupOf c.localActor).map a.action
  have hUne : U ≠ ⊥ := by
    intro h
    have hc := a.module_card
    rw [show (E.V.subgroupOf c.localActor).map a.action = ⊥ from h,card_bot] at hc
    omega
  obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  obtain ⟨v,hv,he⟩ := u.property
  have hane : a.action v ≠ 1 := fun h => hune (Subtype.ext (he.symm.trans h))
  let := E.elementary
  have hv2 : v ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv)
  let α := (MulAut.congr e') (a.action v)
  have hα2 : α ^ 2 = 1 := by
    rw [←map_pow,←map_pow,hv2,map_one,map_one]
  have hαne : α ≠ 1 := by
    intro h
    apply hane
    exact (MulAut.congr e').injective (h.trans (map_one _).symm)
  obtain ⟨x,ho,hl,hi⟩ := BenderSuzuki.MatrixGroups.involution_inverts_large_odd m hm α hα2 hαne
  let y : B := e'.symm x
  have hy : a.action v y = y⁻¹ := by
    apply e'.injective
    simpa only [α,y,MulAut.congr_apply,MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply,map_inv] using hi
  let t := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have horder : orderOf (y : Hstar H) = orderOf x :=
    (Subgroup.orderOf_coe y).trans (e'.symm.orderOf_eq x)
  refine ⟨t,mem_map_of_mem _ hv,y.val,y.property,horder.symm ▸ ho,horder.symm ▸ hl,?_⟩
  exact (a.conjugation v y).symm.trans (congrArg Subtype.val hy)
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
