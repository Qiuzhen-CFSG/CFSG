module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson.Transfer
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson.OffenderGeometry

/-!
# The noncentral orthogonal Thompson alternative

For maximum elementary subgroups of `T`, the transported offender inequality
and the explicit finite-action control imply `image(J(T)) = image(S)`.
The fixed-center identity then gives `E ∩ V = C_V(S)`. Since the Baumann
subgroup centralizes this fixed space, its image lies in the pointwise fixer;
the second finite-action input places it in `image(S)`. The reverse image
containment follows from `J(T) ≤ Baum(T)`, and the kernel gives `Baum(T) ≤ S`.
Order-four elementary groups are identified with the actual coordinate plane
by multiplicative equivalences.

The final theorem `orthogonal_noncentral_of_geometry` discharges both
finite-action inputs using the concrete dihedral Sylow calculation and its
compatible action transport. It retains exactly three geometric hypotheses:
the stabilizer image is elementary abelian of order four, and its fixed plane
has order four. The Section 15.3 assembly owner supplies these geometric
facts. Neither desired Thompson image equalities nor the fixed-center
intersection are used as hypotheses. No family-saturation assertion from
the false general B.1.8(5) is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.5(2)
and the containment used by 15.3.6, printed p.1122.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maxJ_le_baumann (T : Subgroup G) :
    elementaryAbelianMaxJ T ≤ ChapterB.baumann T := by
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj e he
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp he).2.2 j hj |>.symm

omit [Finite G] in
private theorem maxJ_normalized (T : Subgroup G) :
    T ≤ normalizer (elementaryAbelianMaxJ T : Set G) := by
  intro t ht
  have h := T.le_normalizer ht
  rw [mem_normalizer_iff_map_conj_eq] at h ⊢
  change T.map (MulAut.conj t).toMonoidHom = T at h
  change (elementaryAbelianMaxJ T).map (MulAut.conj t).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, h]

/-- A conditional reduction of the noncentral case of 15.3.5 to the indicated
finite natural-action calculation. No Thompson-image equality is assumed. -/
theorem orthogonal_noncentral_image_of_offender_control
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hcontrol : OrthogonalOffenderControl (d.image (T : Subgroup G))
      (d.image (planeStabilizer T (d.plane i)))) :
    d.image (elementaryAbelianMaxJ (T : Subgroup G)) =
        d.image (planeStabilizer T (d.plane i)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M =
        fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let S := planeStabilizer T (d.plane i)
  have hVM := localModule_le T hTM
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJS : J ≤ S := by
    apply sSup_le
    intro A hA
    let _ : IsElementaryAbelian 2 A := hA.2.1
    exact d.le_planeStabilizer_of_image_le T hTM i hA.1
      (hcontrol (d.image A) (d.image_mono hA.1)
        (d.elementary_image (hA.1.trans hTM)) (d.maxElementary_bound T hTM hVM hA)).1
  have hw : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), d.image A ≠ ⊥ := by
    by_contra! h
    apply hJ
    exact sSup_le fun A hA => (d.image_eq_bot_iff (hA.1.trans hTM)).mp (h A hA)
  obtain ⟨A,hA,hAn⟩ := hw
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hSJ : d.image S ≤ d.image J :=
    (hcontrol (d.image A) (d.image_mono hA.1)
      (d.elementary_image (hA.1.trans hTM)) (d.maxElementary_bound T hTM hVM hA)).2
      hAn (d.image J) (d.image_mono (le_sSup hA)) (d.image_mono hJT)
      (d.image_normalizes (maxJ_normalized (T : Subgroup G)))
  have heq : d.image J = d.image S := le_antisymm (d.image_mono hJS) hSJ
  refine ⟨heq, ?_⟩
  rw [d.alpha_inf_eq_fixed T hTM hVM]
  exact d.fixedPlane_eq_of_image_eq (hJT.trans hTM) (inf_le_left.trans hTM) heq

/-- The full noncentral alternative, conditional on two explicitly identified
finite-action facts and the allowed order-four geometry. The theorem
`orthogonal_noncentral_of_geometry` below discharges the finite-action facts. -/
theorem orthogonal_noncentral_of_offender_geometry
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hcontrol : OrthogonalOffenderControl (d.image (T : Subgroup G))
      (d.image (planeStabilizer T (d.plane i))))
    (hfixer : d.image (T : Subgroup G) ⊓
      orthogonalFixedSpaceFixer (d.image (planeStabilizer T (d.plane i))) ≤
        d.image (planeStabilizer T (d.plane i)))
    (helem : IsElementaryAbelian 2 (d.image (planeStabilizer T (d.plane i))))
    (hcard : Nat.card (d.image (planeStabilizer T (d.plane i))) = 4)
    (hfixed : Nat.card (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) = 4) :
    d.image (ChapterB.baumann (T : Subgroup G)) =
        d.image (elementaryAbelianMaxJ (T : Subgroup G)) ∧
      d.image (elementaryAbelianMaxJ (T : Subgroup G)) =
        d.image (planeStabilizer T (d.plane i)) ∧
      Nonempty (d.image (planeStabilizer T (d.plane i)) ≃* OrthogonalPlaneVector) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M =
        fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ∧
      Nonempty (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ≃*
        OrthogonalPlaneVector) ∧
      ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T (d.plane i) := by
  let S := planeStabilizer T (d.plane i)
  let B := ChapterB.baumann (T : Subgroup G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  obtain ⟨himage,hE⟩ := orthogonal_noncentral_image_of_offender_control T d hTM i hJ hcontrol
  have hcent : B ≤ centralizer (fixedPlane (localModule T M) S : Set G) := by
    rw [← hE]
    exact inf_le_right.trans (centralizer_le inf_le_left)
  have hBimage : d.image B ≤ d.image S :=
    (le_inf (d.image_mono (show B ≤ (T : Subgroup G) from inf_le_left))
      (d.image_le_fixedSpaceFixer (inf_le_left.trans hTM) hcent)).trans hfixer
  have hBeq : d.image B = d.image J := le_antisymm
    (hBimage.trans_eq himage.symm) (d.image_mono (maxJ_le_baumann _))
  let _ : IsElementaryAbelian 2 (d.image S) := helem
  let _ : IsElementaryAbelian 2 (fixedPlane (localModule T M) S) := d.elementary_fixedPlane S
  obtain ⟨eS,_⟩ := FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hcard
  obtain ⟨eF,_⟩ := FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hfixed
  exact ⟨hBeq, himage, ⟨eS⟩, hE, ⟨eF⟩,
    d.le_planeStabilizer_of_image_le T hTM i inf_le_left hBimage⟩

/-- The second alternative of 15.3.5 and the containment used by 15.3.6.
The only geometric inputs are elementary abelianness and order four of the
stabilizer image, and order four of its fixed plane. No index-two hypothesis
is needed. The two isomorphism clauses identify the actual groups with the
binary coordinate plane. -/
theorem orthogonal_noncentral_of_geometry
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (helem : IsElementaryAbelian 2 (d.image (planeStabilizer T (d.plane i))))
    (hcard : Nat.card (d.image (planeStabilizer T (d.plane i))) = 4)
    (hfixed : Nat.card (fixedPlane (localModule T M) (planeStabilizer T (d.plane i))) = 4) :
    d.image (ChapterB.baumann (T : Subgroup G)) =
        d.image (elementaryAbelianMaxJ (T : Subgroup G)) ∧
      d.image (elementaryAbelianMaxJ (T : Subgroup G)) =
        d.image (planeStabilizer T (d.plane i)) ∧
      Nonempty (d.image (planeStabilizer T (d.plane i)) ≃* OrthogonalPlaneVector) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M =
        fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ∧
      Nonempty (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ≃*
        OrthogonalPlaneVector) ∧
      ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T (d.plane i) := by
  obtain ⟨hcontrol, hfixer⟩ := d.offender_geometry T hTM i helem hcard hfixed
  exact orthogonal_noncentral_of_offender_geometry T d hTM i hJ hcontrol hfixer
    helem hcard hfixed

end CFSG.Quasithin.Chapter15.Section03

end
