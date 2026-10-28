module

public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Subnormal images in normal direct-power sections

For a subnormal subgroup `B` of a finite group `G`, the intersection with
`O_p(G)` is exactly `O_p(B)`. Thus the image of `B` in `G/O_p(G)` is
isomorphic to `B/O_p(B)`, retaining relative subnormality.

We apply this to a normal subgroup `N` such that `G/N` is a p-group and
`N/O_p(N)` is an actual direct power of a specified group. Every p-perfect
subnormal subgroup of `G` lies in `N`; its p-core quotient is therefore a
subnormal subgroup of that same direct power. Neither the extension over `N`
nor the extension over its p-core is assumed to split.

This is the standard subnormal p-core argument used in the local subgroup
calculations of Aschbacher–Smith, 2.3.9(7), printed p.526. It is independent
of the local groups or block types used in that application.
-/

@[expose] public section

open Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A subnormal subgroup meets the ambient p-core in its intrinsic p-core. -/
theorem IsSubnormal.pCore_subgroupOf {B : Subgroup G}
    (hB : B.IsSubnormal) (p : ℕ) :
    (pCore p G).subgroupOf B = pCore p B := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  · have hm := pCoreAmbient_mono_of_isSubnormalIn B ⊤ p le_top
      (hB.comap (⊤ : Subgroup G).subtype)
    have he : (pCore p (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pCore p G :=
      pCore_map_iso p Subgroup.topEquiv
    rw [he] at hm
    intro x hx
    exact hm ⟨x, hx, rfl⟩

/-- The subnormal quotient is the actual image in the ambient p-core quotient. -/
noncomputable def IsSubnormal.quotientCoreImageEquiv {B : Subgroup G}
    (hB : B.IsSubnormal) (p : ℕ) :
    (B ⧸ pCore p B) ≃* B.map (QuotientGroup.mk' (pCore p G)) := by
  let f := (QuotientGroup.mk' (pCore p G)).comp B.subtype
  have hk : f.ker = pCore p B := by
    change ((QuotientGroup.mk' (pCore p G)).comp B.subtype).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hB.pCore_subgroupOf p
  have hr : f.range = B.map (QuotientGroup.mk' (pCore p G)) := by
    simp only [f, MonoidHom.range_comp, range_subtype]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))

end Subgroup

namespace Theory.GroupTheory

/-- A normal section identified with an actual direct power. The overgroup
quotient is a p-group; both possible nonsplit extensions are retained. -/
structure NormalDirectPowerSection (p : ℕ) (G A : Type*) [Group G] [Group A] where
  base : Subgroup G
  normal : base.Normal
  quotient_isPGroup : @IsPGroup p (G ⧸ base) (@QuotientGroup.Quotient.group G _ base normal)
  copies : ℕ
  quotientIso : (base ⧸ pCore p base) ≃* (Fin copies → A)

namespace NormalDirectPowerSection

variable {p : ℕ} {G A : Type*} [Group G] [Group A]

/-- A p-perfect subgroup is contained in every normal subgroup of p-power index. -/
theorem le_base (d : NormalDirectPowerSection p G A)
    (B : Subgroup G) (hB : IsPPerfect p B) : B ≤ d.base :=
  (le_pResidual_of_isPPerfect B hB).trans (sInf_le ⟨d.normal, d.quotient_isPGroup⟩)

/-- A p-perfect subnormal subgroup gives a subnormal subgroup of the specified
direct power, isomorphic to its quotient by its own p-core. -/
theorem exists_subnormal_quotient_image [Finite G]
    (d : NormalDirectPowerSection p G A) (B : Subgroup G)
    (hB : B.IsSubnormal) (hp : IsPPerfect p B) :
    ∃ I : Subgroup (Fin d.copies → A), I.IsSubnormal ∧
      Nonempty ((B ⧸ pCore p B) ≃* I) := by
  let B' := B.subgroupOf d.base
  have hB' : B'.IsSubnormal := hB.subgroupOf
  let eB : B' ≃* B := subgroupOfEquivOfLe (d.le_base B hp)
  let eQ := QuotientGroup.congr (pCore p B') (pCore p B) eB (pCore_map_iso p eB)
  let I' := B'.map (QuotientGroup.mk' (pCore p d.base))
  let I := I'.map d.quotientIso.toMonoidHom
  refine ⟨I, (hB'.map (QuotientGroup.mk'_surjective _)).map d.quotientIso.surjective, ?_⟩
  exact ⟨eQ.symm.trans ((hB'.quotientCoreImageEquiv p).trans
    (d.quotientIso.subgroupMap I'))⟩

end NormalDirectPowerSection
end Theory.GroupTheory
