module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.DisplacementFamily
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceDisplacement

/-!
# The corrected G₂ displacement-family normalizer application

The full second preimage is characterized by Sylow displacement into V1.
Sylow conjugacy gives its entire L1-orbit; the preceding interval incidence
restricts that description to V3. The intrinsic identity V1=C_{V3}(L1)
then forces N_G(V3) intersect N_G(L1) to permute these planes. The genuine
plane-component uniqueness and residual generation feed the existing
normalizes_of_plane_permutation theorem, giving both clauses of the source
NormalizerControl with the original central kernel retained.

The point-residual image and interval incidence belong to the independent
G₂ residual-incidence construction. Component uniqueness and residual
generation also remain explicit: this is a conditional source application,
not a completed proof of 11.1.4 from the standing chapter hypotheses.

Source: Aschbacher--Smith 11.1.4, printed p.765; the displacement model uses
I.2.3, p.413, and the flag definitions on pp.760--761.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private theorem seed_normalizes_first : V ≤ normalizer ((flag S m).Vi 0 : Set G) := by
  let := D.elementary
  exact ((le_centralizer_iff_isMulCommutative.mpr inferInstance :
    V ≤ centralizer (V : Set G)).trans
      (centralizer_le (D.centralQuotientPreimage_le _))).trans (Subgroup.centralizer_le_normalizer _)

/-- The actual base plane is the displacement subgroup modulo V1. -/
theorem second_eq_displacement
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m) :
    (flag S m).Vi 1 = Displacement.subgroup V ((flag S m).Vi 0)
      ((P : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype) := by
  ext v
  rw [Displacement.mem_subgroup (seed_normalizes_first S m)]
  constructor
  · intro hv
    have hV := D.centralQuotientPreimage_le _ hv
    refine ⟨hV, ?_⟩
    rintro p ⟨q,hq,rfl⟩
    exact (mem_second_iff_displacement S m P hP ⟨v,hV⟩).mp hv ⟨q,hq⟩
  · rintro ⟨hV,hv⟩
    apply (mem_second_iff_displacement S m P hP ⟨v,hV⟩).mpr
    intro p
    exact hv _ (mem_map_of_mem _ p.property)

/-- The correct plane family is displacement modulo V1, restricted to V3.
The interval incidence is precisely the preceding residual-incidence input. -/
theorem planeOrbit_eq_displacement
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m)
    (hinterval : ∀ U ∈ Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      (flag S m).Vi 0 ≤ U ∧ U ≤ (flag S m).Vi 2) :
    Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0) =
      Set.range (fun Q : Sylow 2 ((flag S m).Li 0) =>
        Displacement.subgroup ((flag S m).Vi 2) ((flag S m).Vi 0)
          ((Q : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype)) := by
  have he : Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0) =
      Set.range (fun Q : Sylow 2 ((flag S m).Li 0) =>
        Displacement.subgroup V ((flag S m).Vi 0)
          ((Q : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype)) :=
    Displacement.orbit_eq_range
    (((localResidual_le _).trans inf_le_left).trans D.normalizes)
    ((localResidual_le _).trans inf_le_right) P (second_eq_displacement S m P hP)
  have hr (Q : Sylow 2 ((flag S m).Li 0)) :
      Displacement.subgroup ((flag S m).Vi 2) ((flag S m).Vi 0)
        ((Q : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype) =
      Displacement.subgroup V ((flag S m).Vi 0)
        ((Q : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype) := by
    apply Displacement.restrict_eq (D.centralQuotientPreimage_le _)
    apply (hinterval _ _).2
    rw [he]
    exact ⟨Q,rfl⟩
  simpa only [hr] using he

/-- Membership in each member of the repaired family is the literal ambient commutator condition. -/
theorem mem_plane_displacement (P : Sylow 2 ((flag S m).Li 0)) (v : G) :
    v ∈ Displacement.subgroup ((flag S m).Vi 2) ((flag S m).Vi 0)
      ((P : Subgroup ((flag S m).Li 0)).map ((flag S m).Li 0).subtype) ↔
    v ∈ (flag S m).Vi 2 ∧ ∀ p : P,
      (p.val.val : G) * v * (p.val.val : G)⁻¹ * v⁻¹ ∈ (flag S m).Vi 0 := by
  have hn : (flag S m).Vi 2 ≤ normalizer ((flag S m).Vi 0 : Set G) :=
    (D.centralQuotientPreimage_le _).trans (seed_normalizes_first S m)
  rw [Displacement.mem_subgroup hn]
  apply and_congr_right'
  constructor
  · intro h p
    exact h _ (mem_map_of_mem _ p.property)
  · rintro h _ ⟨p,hp,rfl⟩
    exact h ⟨p,hp⟩

/-- The two ambient normalizers permute Delta through intrinsic V1 and Sylow displacement. -/
theorem normalizer_permutes_planes
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m)
    (hinterval : ∀ U ∈ Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      (flag S m).Vi 0 ≤ U ∧ U ≤ (flag S m).Vi 2)
    {g : G} (hg : g ∈ normalizer ((flag S m).Vi 2 : Set G) ⊓
      normalizer ((flag S m).Li 0 : Set G)) :
    ∀ U ∈ Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      U.map (MulAut.conj g).toMonoidHom ∈
        Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0) := by
  intro U hU
  rw [planeOrbit_eq_displacement S m P hP hinterval] at hU ⊢
  obtain ⟨Q,rfl⟩ := hU
  obtain ⟨R,hR⟩ := Displacement.normalizer_permutes hg.1
    (normalizer_preserves_first S m P hP hg) hg.2 Q
  exact ⟨R,hR.symm⟩

/-- Both source normalizer containments, with genuine earlier component uniqueness
and residual generation retained. No ordinary-Sylow-fixed-family premise is used. -/
theorem normalizerControl_of_displacement
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m)
    (hunique : Source.UniqueNoncentralComponent
      (normalizer ((flag S m).Vi 1 : Set G)) ((flag S m).Vi 1) ((flag S m).Li 1))
    (hgen : L = ⨆ U : Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      localResidual L U.val)
    (hinterval : ∀ U ∈ Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      (flag S m).Vi 0 ≤ U ∧ U ≤ (flag S m).Vi 2) :
    Source.NormalizerControl ((flag S m).Vi 2) ((flag S m).Vi 0) ((flag S m).Li 0)
      (normalizer (L : Set G)) := by
  have hL : (flag S m).Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hc := Normalizers.orbit_unique hL hunique
  constructor
  · intro g hg
    apply Normalizers.normalizes_of_plane_permutation hc hgen
    intro U hU
    rwa [Normalizers.sectionCentralizer_fixes (hinterval U hU).1 (hinterval U hU).2 hg]
  · intro g hg
    exact Normalizers.normalizes_of_plane_permutation hc hgen
      (normalizer_permutes_planes S m P hP hinterval hg)

/-- Assembly can supply just the concrete point-residual image containment;
the Sylow lift and all displacement/normalizer transport are then automatic. -/
theorem normalizerControl_of_point_image
    (himage : (modelSylow S m : Subgroup _) ≤ (pointMap S m).range)
    (hunique : Source.UniqueNoncentralComponent
      (normalizer ((flag S m).Vi 1 : Set G)) ((flag S m).Vi 1) ((flag S m).Li 1))
    (hgen : L = ⨆ U : Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      localResidual L U.val)
    (hinterval : ∀ U ∈ Normalizers.planeOrbit ((flag S m).Vi 1) ((flag S m).Li 0),
      (flag S m).Vi 0 ≤ U ∧ U ≤ (flag S m).Vi 2) :
    Source.NormalizerControl ((flag S m).Vi 2) ((flag S m).Vi 0) ((flag S m).Li 0)
      (normalizer (L : Set G)) := by
  obtain ⟨P,hP⟩ := exists_pointSylow S m himage
  exact normalizerControl_of_displacement S m P hP hunique hgen hinterval

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
