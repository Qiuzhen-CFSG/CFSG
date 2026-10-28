module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The centralizing choice is different from the full residual

A simultaneous order-three rotation belongs to the literal two-residual
of the orthogonal actor and moves a vector in each definite plane.
The compatible full-image hypothesis 15.3.7 therefore prevents Y from
centralizing either plane. The CaseTwo residual centralizes V₁, so it
cannot be Y. This discharges the conditional V₁ clause of PlaneActorPair.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10(2), and the conditional interchange in 15.3.40, printed
pp.1122–1123 and 1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

open scoped Matrix
private def planeRotation : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩

private def constantBase : OrthogonalPlaneActor →* OrthogonalActor where
  toFun r := ⟨fun _ => r, 1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem planeRotation_cube : planeRotation ^ 3 = 1 := by decide +kernel

private theorem full_residual_moves_plane (i : OrthogonalPlaneIndex) :
    letI := orthogonalAction
    ∃ a ∈ Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor),
      ∃ v ∈ orthogonalCoordinatePlane i, a • v ≠ v := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  let a := constantBase planeRotation
  have ha3 : a ^ 3 = 1 := by
    rw [← map_pow, planeRotation_cube, map_one]
  have ha : a ∈ pResidual 2 OrthogonalActor :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha3))
  have hr : Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) =
      pResidual 2 OrthogonalActor := by
    unfold Stellmacher.twoResidualAmbient
    have he : Stellmacher.twoResidualSubgroup (⊤ : Subgroup OrthogonalActor) =
        pResidual 2 (⊤ : Subgroup OrthogonalActor) := by
      unfold Stellmacher.twoResidualSubgroup pResidual
      congr 1
      ext N
      constructor
      · rintro ⟨hN,n,hn⟩
        let := hN
        exact ⟨hN, IsPGroup.of_card (by simpa only [index_eq_card] using hn)⟩
      · rintro ⟨hN,hp⟩
        let := hN
        obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp hp
        exact ⟨hN,n,by simpa only [index_eq_card] using hn⟩
    rw [he]
    exact map_pResidual 2 (Subgroup.topEquiv : (⊤ : Subgroup OrthogonalActor) ≃* OrthogonalActor)
  let u : OrthogonalPlaneVector := Multiplicative.ofAdd ![1, 0]
  let v : OrthogonalVector := fun j => if j = i then u else 1
  refine ⟨a, hr.symm ▸ ha, v, (fun j hj => if_neg hj), ?_⟩
  intro he
  have hh := congrFun he i
  change planeRotation • v (1⁻¹ * i) = v i at hh
  simp only [inv_one, one_mul, v, if_pos rfl] at hh
  have hn : planeRotation • u ≠ u := by decide +kernel
  exact hn hh

/-- The full residual action moves each definite plane, so the CaseTwo
centralizing residual is strictly different from Y. -/
theorem caseTwo_ne_residualY_of_full_image {M Mc V S Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex)
    (hcase : CaseTwo M (residualY M Mc) S (d.plane i) Yplus)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Yplus ≠ residualY M Mc := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro heq
  have hYC : residualY M Mc ≤ centralizer (d.plane i : Set G) := by
    rw [← heq, hcase.2]
    exact (map_subtype_le _).trans inf_le_right
  obtain ⟨a,ha,v,hv,hmove⟩ := full_residual_moves_plane i
  rw [← h7] at ha
  obtain ⟨m,hm,hma⟩ := ha
  let w := d.coordinates.symm v
  have hw : (w : G) ∈ d.plane i := by
    exact mem_map.mpr ⟨w, by simpa [w] using hv, rfl⟩
  have hmw : V.normalizerMonoidHom ⟨m,d.normalizes m.property⟩ w = w := by
    apply Subtype.ext
    change (m : G) * (w : G) * (m : G)⁻¹ = w
    exact mul_inv_eq_iff_eq_mul.mpr ((hYC hm) w hw).symm
  apply hmove
  have hh := d.compatible m w
  rw [hmw, hma] at hh
  simpa only [w, MulEquiv.apply_symm_apply] using hh.symm

end CFSG.Quasithin.Chapter15.Section03.RankTwo
