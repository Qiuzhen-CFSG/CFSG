module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Full-core action on a local short subgroup

A local C-component is subnormal in its join with the prescribed full Sylow.
That join contains the ambient two-core. The subnormal two-perfect action
lemma puts its entire core commutator inside the block's elementary layer.
Thus every element of the ambient core commutator has square one.

This is the exact local, rather than globally subnormal, form needed by the
rank-two parabolic escape in Aschbacher--Smith 2.4.25 (printed p.543), using
A.3.10 and C.1.7. It uses no Sylow index bound.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A short member of the full-Sylow local C-component family has elementary
commutator with the entire ambient two-core. -/
theorem local_short_core_commutator_square (S : Sylow 2 G) (B : Subgroup G)
    (hb : IsShort B) (hl : B ∈ ChapterA.Section03.localCComponents S)
    {x : G} (hx : x ∈ ⁅pCore 2 G, B⁆) : x ^ 2 = 1 := by
  let H := B ⊔ (S : Subgroup G)
  let B' := B.subgroupOf H
  have hBH : B ≤ H := le_sup_left
  let eB : B' ≃* B := subgroupOfEquivOfLe hBH
  have hp' : IsPPerfect 2 B' := hb.twoPerfect.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  have heB : (blockU B').map eB.toMonoidHom = blockU B := by
    rw [blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ eB.surjective, blockU]
  have hs : B'.IsSubnormal := hl.subnormal
  have hQH : pCore 2 G ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right
  let Q := (pCore 2 G).subgroupOf H
  have hnorm : B' ≤ normalizer Q := le_normalizer_of_normal
  have hc : ⁅Q, B'⁆ ≤ (blockU B').map B'.subtype :=
    commutator_le_core_commutator_of_isSubnormal B' Q hs hp'
      pCore_isPGroup.comap_subtype hnorm
  have he : (⁅Q, B'⁆).map H.subtype = ⁅pCore 2 G, B⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hQH,
      map_subgroupOf_eq_of_le hBH]
  rw [← he] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨u, hu, he⟩ := hc hy
  have hum : eB u ∈ blockU B := heB ▸ mem_map_of_mem eB.toMonoidHom hu
  have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    hb.elementary.exponent_dvd_p (⟨eB u, hum⟩ : blockU B)
  have hy : (y : G) = (eB u : G) := congrArg H.subtype he.symm
  change (y : G) ^ 2 = 1
  rw [hy]
  exact congrArg (fun t : blockU B => ((t : B) : G)) hpow

end CFSG.Quasithin.ChapterC
