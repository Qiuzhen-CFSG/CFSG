module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Algebra

/-!
# Residual control after saturation

The actual continuation span is nontrivial modulo Q_c by its stipulated image
index. Inside the finite center stabilizer, normal generation in the original
SL3(2) quotient extends a radius commutator bound to the two-residual. Both
normalities are relative to that stabilizer, and its projection is exactly the
one in the selected frame.

The center commutator identity also puts the generated endpoint plane inside
Z_c. Once V_c = (V_c intersect Q_b) W, this plane and the normality of W give
[V_c,V0] <= W. The saturation equality is proved in the companion modules.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891;
residual extension uses the checked local-product algebra of (4.3.2).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c} (w : s.Continuation)

/-- The source residual step inside the finite center stabilizer, using the original projection. -/
theorem moving_le_span_of_radius_commutator (source : LocalSource L R)
    (hb : 4 < geometry.b R)
    (hindex : (Q R s.center).relIndex (s.continuationSpan w) = 4)
    (hc : ⁅V R s.center, s.continuationSpan w⁆ ≤ localZSpan R s.start s.center) :
    Vcirc R s.center ≤ localZSpan R s.start s.center := by
  let S := stabilizer R s.center
  let := finite_stabilizer R s.center
  let H := (V R s.center).subgroupOf S
  let W := (localZSpan R s.start s.center).subgroupOf S
  let J := (s.continuationSpan w).subgroupOf S
  let π := s.frame.sectionData.projection
  have hHS : V R s.center ≤ S :=
    (geometry.V_le_Q (by omega) s.center (s.center_color (by omega))).trans (fun _ hx => hx.1)
  have hWS : localZSpan R s.start s.center ≤ S := s.frame.sectionData.local_group
  have hJS := w.span_le_center_stabilizer (by omega : 2 ≤ geometry.b R)
  let : H.Normal := normal_subgroupOf_of_le_normalizer (V_normalized R s.center)
  let : W.Normal := localZSpan_normal R s.start s.center
  have hker : IsPGroup 2 π.ker := by
    rw [s.frame.sectionData.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le s.center
      (s.center_color (by omega))).comap_subtype
  have hpH : IsPGroup 2 H :=
    ((Q_isPGroup R source.two_group source.core_le s.center (s.center_color (by omega))).to_le
      (geometry.V_le_Q (by omega) s.center (s.center_color (by omega)))).comap_subtype
  have hJ : ¬ J ≤ π.ker := by
    intro h
    have hle : s.continuationSpan w ≤ Q R s.center := by
      intro x hx
      have h' := h (show (⟨x, hJS hx⟩ : S) ∈ J from hx)
      rw [s.frame.sectionData.module_section.projection_kernel] at h'
      exact h'
    have he := relIndex_eq_one.mpr hle
    omega
  have hcomm : ⁅H, J⁆ ≤ W := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hHS, map_subgroupOf_eq_of_le hJS]
    exact hc
  have hh := map_mono (f := S.subtype)
    (Escape.PairingControl.Geometry.LocalProducts.residual_commutator_bound
      π s.frame.sectionData.module_section.projection_surjective hker H W J hpH hJ hcomm)
  dsimp only [H, W] at hh
  have hres : Vcirc R s.center ≤ ⁅localZSpan R s.start s.center, Ltilde R s.center⁆ := by
    simpa only [map_commutator, map_subgroupOf_eq_of_le hHS,
      map_subgroupOf_eq_of_le hWS, Vcirc, Ltilde, S] using hh
  exact hres.trans (le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer s.center).trans (localZSpan_normalized R s.start s.center)))

include w in
/-- Locality and the full center displacement place the generated endpoint plane in Z_c. -/
theorem endpointSpan_le_center_Z (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : s.endpointSpan ≤ Z R s.center := by
  rw [← w.center_commutator_eq common hb]
  exact le_normalizer_iff_commutator_le_left.mp
    ((w.span_le_center_stabilizer (by omega)).trans (Z_normalized R s.center))

/-- Saturation extends the proved radius/kernel commutator bound to the entire center radius. -/
theorem radius_commutator_le_span_of_saturation (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hsat : V R s.center = (V R s.center ⊓ Q R s.endpoint) ⊔
      localZSpan R s.start s.center) :
    ⁅V R s.center, s.continuationSpan w⁆ ≤ localZSpan R s.start s.center := by
  have hnorm := (w.span_le_center_stabilizer (by omega)).trans
    (localZSpan_normalized R s.start s.center)
  have hnormV := ((geometry.V_le_Q (by omega) s.center (s.center_color (by omega))).trans
    (show Q R s.center ≤ stabilizer R s.center from fun _ hx => hx.1)).trans
      (localZSpan_normalized R s.start s.center)
  apply (commutator_mono (H₁ := V R s.center) ?_ le_rfl).trans
    (commutator_commutatorPreimage_le (V R s.center) (s.continuationSpan w)
      (localZSpan R s.start s.center) hnormV)
  apply hsat.le.trans
  apply sup_le
  · apply le_commutatorPreimage inf_le_left
    exact (w.radius_commutator common hb).trans
      ((w.endpointSpan_le_center_Z common hb).trans
        (center_Z_le_span (s.center_color (by omega)) (s.center_distance (by omega))))
  · exact le_commutatorPreimage (localZSpan_le_V R (s.center_distance (by omega)).le)
      (le_normalizer_iff_commutator_le_left.mp hnorm)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
