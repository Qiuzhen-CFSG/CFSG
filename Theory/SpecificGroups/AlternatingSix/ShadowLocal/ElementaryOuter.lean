module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
/-!
# Elementary subgroups have at most two outer cosets in Aut(A₆)

In the marked Sylow holomorph, two commuting involutions outside the inner
dihedral subgroup have inner product. Thus every elementary subgroup has at
most two inner cosets. The marked Sylow equivalence transports this statement
to the actual automorphism group, retaining its literal inner subgroup.

Source: Aschbacher–Smith, original 14.6.24(2), printed p.1041. Together with
simultaneous quadraticity on the two A₆ covers, this bounds the whole actor
by order four; see AlternatingSixPairedCovers.QuadraticActors.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal
namespace Holomorph
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem outside_product : ∀ x y : Model,
    x ^ 2 = 1 → y ^ 2 = 1 → x*y = y*x →
    (¬ ∃ d, innerEmbedding d = x) → (¬ ∃ d, innerEmbedding d = y) →
    ∃ d, innerEmbedding d = x*y := by decide +kernel

/-- An elementary subgroup of the holomorph has at most two inner cosets. -/
theorem elementary_inner_relIndex (E : Subgroup Model) [IsElementaryAbelian 2 E] :
    innerD.relIndex E ≤ 2 := by
  apply Nat.le_of_dvd (by decide)
  apply (innerD.subgroupOf E).index_dvd_two_iff.mpr
  by_cases he : ∃ x : E, (x : Model) ∉ innerD
  · obtain ⟨x,hx⟩ := he
    refine ⟨x,fun y => ?_⟩
    by_cases hy : (y : Model) ∈ innerD
    · exact Or.inr hy
    · left
      exact (mem_innerD _).mpr (outside_product y x
        (elemPow_eq_one_of_isElementaryAbelian _ y.property)
        (elemPow_eq_one_of_isElementaryAbelian _ x.property)
        (congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm y x))
        (fun h => hy ((mem_innerD _).mpr h)) (fun h => hx ((mem_innerD _).mpr h)))
  · exact ⟨1,fun y => Or.inr (by by_contra hn; exact he ⟨y,hn⟩)⟩
end Holomorph

/-- Every elementary subgroup of Aut(A₆) has at most two inner cosets.
The quotient Out(A₆) has order four; elementary lifts cannot cover all four. -/
theorem elementary_inner_relIndex (E : Subgroup AutA6) [IsElementaryAbelian 2 E] :
    inner.relIndex E ≤ 2 := by
  obtain ⟨P,hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let e := Identification.sylowEquiv P
  let F := (E.subgroupOf (P : Subgroup AutA6)).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (E.subgroupOf (P : Subgroup AutA6)) :=
    IsElementaryAbelian.subgroupOf hEP
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hF := Holomorph.elementary_inner_relIndex F
  have hm : F.map e.toMonoidHom = E.subgroupOf (P : Subgroup AutA6) :=
    e.mapSubgroup.apply_symm_apply _
  rw [← relIndex_map_map_of_injective (f := e.toMonoidHom) Holomorph.innerD F e.injective,
    Identification.sylowEquiv_innerD,hm] at hF
  change (inner.comap (P : Subgroup AutA6).subtype).relIndex
    (E.subgroupOf (P : Subgroup AutA6)) ≤ 2 at hF
  rw [relIndex_comap,Subgroup.map_subgroupOf_eq_of_le hEP] at hF
  exact hF
end AlternatingSix.ShadowLocal
