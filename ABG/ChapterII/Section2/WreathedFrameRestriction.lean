module
public import ABG.ChapterII.Section2.SylowShapeTransport
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Restricting a wreathed fusion frame

A subgroup containing the chosen wreathed Sylow two-subgroup inherits its
entire fusion frame by restriction. The result retains the same height,
the unique abelian maximal base, and the actual quaternion-center join.
No finiteness assumption on the ambient group is needed.

The subtype Sylow group is canonically isomorphic to the original one.
Transport its wreathed presentation and the base's maximality through that
isomorphism. Its subgroup order isomorphism transfers uniqueness among all
abelian maximal subgroups. Transport of the center's actual ambient image
and restriction of subgroup joins preserve the chosen quaternion-center
product, rather than replacing it with a fresh model.

This is the frame-restriction step in Alperin--Brauer--Gorenstein,
Chapter II, Section 2, Proposition 1 (article page 15), when passing to an
involution centralizer. The corresponding quasi-dihedral restriction is
proved in QuasiFrameTransport; automizer restrictions are separate lemmas.
-/

namespace ABG
open Subgroup

private theorem subgroupCenter_subgroupOf
    {G : Type*} [Group G] (S H : Subgroup G) (hSH : S ≤ H) :
    subgroupCenter (S.subgroupOf H) = (subgroupCenter S).subgroupOf H := by
  let e : S.subgroupOf H ≃* S := Subgroup.subgroupOfEquivOfLe hSH
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro z
    simpa only [map_mul, e.apply_symm_apply] using
      congrArg e (mem_center_iff.mp hy (e.symm z))
  · rintro ⟨y, hy, hyx⟩
    refine ⟨e.symm y, ?_, Subtype.ext hyx⟩
    apply mem_center_iff.mpr
    intro z
    simpa only [map_mul, e.symm_apply_apply] using
      congrArg e.symm (mem_center_iff.mp hy (e z))

/-- Restrict the entire wreathed frame to a subgroup containing its Sylow subgroup. -/
public theorem wreathedFusionFrame_subtype
    {G : Type*} [Group G] (S : Sylow 2 G) (n : ℕ) (U V H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hframe : WreathedFusionFrame S n U V) :
    WreathedFusionFrame (S.subtype hSH) n (U.subgroupOf H) (V.subgroupOf H) := by
  obtain ⟨hS, hUS, hUcomm, hUmax, huniq, Q, hQS, hQ, hV⟩ := hframe
  let R : Sylow 2 H := S.subtype hSH
  let e : R ≃* S := Subgroup.subgroupOfEquivOfLe hSH
  have hUeq : (U.subgroupOf H).subgroupOf R = (U.subgroupOf S).comap e.toMonoidHom := rfl
  let : IsMulCommutative U := hUcomm
  refine ⟨wreathed_equiv e.symm hS, subgroupOf_mono H hUS, inferInstance, ?_, ?_, ?_⟩
  · change IsCoatom ((U.subgroupOf H).subgroupOf R)
    rw [hUeq]
    exact (Subgroup.isCoatom_comap e).mpr hUmax
  · intro W hWcomm hWmax
    let : IsMulCommutative W := hWcomm
    have hm : W.map e.toMonoidHom = U.subgroupOf S :=
      huniq (W.map e.toMonoidHom) inferInstance
        ((OrderIso.isCoatom_iff e.mapSubgroup W).mpr hWmax)
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    change W.map e.toMonoidHom = ((U.subgroupOf H).subgroupOf R).map e.toMonoidHom
    rw [hm, hUeq, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  · refine ⟨Q.subgroupOf H, subgroupOf_mono H hQS, ?_, ?_⟩
    · obtain ⟨eQ⟩ := hQ
      exact ⟨(Subgroup.subgroupOfEquivOfLe (hQS.trans hSH)).trans eQ⟩
    · have hcH : subgroupCenter (S : Subgroup G) ≤ H :=
        (Subgroup.map_subtype_le (center (S : Subgroup G))).trans hSH
      rw [hV, Subgroup.subgroupOf_sup (hQS.trans hSH) hcH]
      congr 1
      exact (subgroupCenter_subgroupOf (S : Subgroup G) H hSH).symm

end ABG

