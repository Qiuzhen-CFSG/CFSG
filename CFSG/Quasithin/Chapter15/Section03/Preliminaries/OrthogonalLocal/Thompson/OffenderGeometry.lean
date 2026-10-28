module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson.OffenderGeometry.Marking

/-!
# Offender and fixed-space control for the natural orthogonal action

Conjugacy with the concrete dihedral Sylow subgroup supplies an actual
marking of any Sylow two-subgroup of the orthogonal actor. Acting by the
same conjugating element on vectors makes this marking equivariant, so the
standard-model offender calculation and pointwise-fixer bound transport to
the given Sylow subgroup.

An elementary subgroup of order four with four common fixed vectors is
then the marked base four-group. For the image of the ambient plane
stabilizer, the existing fixed-space equivalence supplies exactly this
fixed-vector order. The final theorem provides both finite-action inputs
of `orthogonal_noncentral_of_offender_geometry`; its elementary and order
hypotheses remain for the source assembly owner to discharge. No Thompson
or Baumann image equality is assumed. The optional index-two premise is
not needed for these finite-action deductions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.5,
printed p.1122, and the preceding definite-plane decomposition.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
open OrthogonalOffenderGeometry

/-- The finite-action control for every Sylow subgroup, using actual action conjugacy. -/
theorem orthogonal_sylow_offender_geometry (P : Sylow 2 OrthogonalActor)
    (Q : Subgroup OrthogonalActor) (hQP : Q ≤ (P : Subgroup OrthogonalActor))
    (hQe : IsElementaryAbelian 2 Q) (hQc : Nat.card Q = 4)
    (hQf : Nat.card (orthogonalFixedVectors Q) = 4) :
    OrthogonalOffenderControl (P : Subgroup OrthogonalActor) Q ∧
      (P : Subgroup OrthogonalActor) ⊓ orthogonalFixedSpaceFixer Q ≤ Q := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  let f : D →* OrthogonalActor := (MulAut.conj g).toMonoidHom.comp wreathTwoDihedralHom
  let e : OrthogonalVector ≃ OrthogonalVector := MulAction.toPerm g
  have hf : Function.Injective f := (MulAut.conj g).injective.comp wreathTwoDihedralHom_injective
  have he : ∀ x v, f x • e v = e (wreathTwoDihedralHom x • v) := by
    intro x v
    change (g * wreathTwoDihedralHom x * g⁻¹) • (g • v) = g • (wreathTwoDihedralHom x • v)
    rw [mul_smul, mul_smul, inv_smul_smul]
  have hrange : f.range = (P : Subgroup OrthogonalActor) := by
    rw [← hg, Sylow.coe_subgroup_smul, wreathTwoSylow_coe]
    exact MonoidHom.range_comp (MulAut.conj g).toMonoidHom wreathTwoDihedralHom
  have hbase : Q = dihedralBase.map f :=
    marked_base_eq f hf e he Q (hQP.trans_eq hrange.symm) hQe hQc hQf
  rw [hbase, ← hrange]
  exact ⟨marked_offender_control f hf e he, marked_fixer_control f e he⟩

/-- The two finite-action inputs consumed by the noncentral Thompson assembly.
Only the authorized elementary/order-four geometry remains as input. -/
theorem NaturalOrthogonalAction.offender_geometry
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (helem : IsElementaryAbelian 2 (d.image (planeStabilizer T (d.plane i))))
    (hcard : Nat.card (d.image (planeStabilizer T (d.plane i))) = 4)
    (hfixed : Nat.card (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) = 4) :
    OrthogonalOffenderControl (d.image (T : Subgroup G))
        (d.image (planeStabilizer T (d.plane i))) ∧
      d.image (T : Subgroup G) ⊓
        orthogonalFixedSpaceFixer (d.image (planeStabilizer T (d.plane i))) ≤
          d.image (planeStabilizer T (d.plane i)) := by
  have hfixed' : Nat.card (orthogonalFixedVectors (d.image (planeStabilizer T (d.plane i)))) = 4 :=
    (Nat.card_congr (d.fixedEquiv (show planeStabilizer T (d.plane i) ≤ M from
      inf_le_left.trans hTM)).toEquiv).symm.trans hfixed
  exact orthogonal_sylow_offender_geometry (d.imageSylow T hTM)
    (d.image (planeStabilizer T (d.plane i))) (d.image_mono inf_le_left) helem hcard hfixed'

end CFSG.Quasithin.Chapter15.Section03

end
