module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Moving.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Moving.Duality

/-!
# The actual opposite quotient and its kernel intersection

The chosen continuation is elementary abelian. Its image in the original
marked center quotient has order four under the stipulated image-index
hypothesis. The already proved natural displacement has order four, so duality
computes a fixed subgroup of order two on the literal WB_c/B_c.

The radius commutator bound puts the image of W intersect Q_b in that fixed
subgroup: its commutator lies in the generated plane K <= Z_c <= B_c. The same
marked coordinates therefore give [W : W intersect Q_b] >= 4. Together with
the endpoint image bound this supplies saturation, without an action premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c} (w : s.Continuation)

omit [Finite M] in
/-- The continuation span inherits elementary abelianness from the endpoint radius group. -/
theorem span_elementary (hb : 4 < geometry.b R) :
    IsElementaryAbelian 2 (s.continuationSpan w) := by
  let := V_elementary_of_four_lt R s.path.end_color hb
  exact IsElementaryAbelian.of_le (w.span_le_radius (by omega))

omit [Finite M] in
/-- The image is elementary under the original projection and the natural factor marking. -/
theorem span_marked_image_elementary (hb : 4 < geometry.b R) :
    IsElementaryAbelian 2 (((s.continuationSpan w).subgroupOf (stabilizer R s.center)).map
      (s.frame.naturalU.marking.toMonoidHom.comp s.frame.sectionData.projection)) := by
  let := w.span_elementary hb
  let := IsElementaryAbelian.subgroupOf (p := 2) (w.span_le_center_stabilizer (by omega : 2 ≤ geometry.b R))
  exact IsElementaryAbelian.map _

omit [Finite M] in
/-- The stipulated image index gives order four with both original markings retained. -/
theorem span_marked_image_card (hb : 4 < geometry.b R)
    (hindex : (Q R s.center).relIndex (s.continuationSpan w) = 4) :
    Nat.card (((s.continuationSpan w).subgroupOf (stabilizer R s.center)).map
      (s.frame.naturalU.marking.toMonoidHom.comp s.frame.sectionData.projection)) = 4 := by
  rw [← map_map, card_map_of_injective s.frame.naturalU.marking.injective,
    ← relIndex_ker, s.frame.sectionData.module_section.projection_kernel,
    relIndex_subgroupOf (w.span_le_center_stabilizer (by omega : 2 ≤ geometry.b R))]
  exact hindex

/-- The actual continuation fixes exactly two elements on the literal WB_c/B_c. -/
theorem barSpan_fixed_card_two (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    Nat.card (barSpan geometry s.start s.center ⊓ centralizer
      (((s.continuationSpan w).subgroupOf (stabilizer R s.center)).map
        (fixedQuotientMap geometry s.center) : Set (FixedQuotient geometry s.center)) :
          Subgroup (FixedQuotient geometry s.center)) = 2 := by
  let S := stabilizer R s.center
  let := finite_stabilizer R s.center
  let := fixed_normal (geometry := geometry) s.center
  let J := (s.continuationSpan w).subgroupOf S
  have hJS : s.continuationSpan w ≤ S := w.span_le_center_stabilizer (by omega)
  let := w.span_elementary hb
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.subgroupOf hJS
  have hUS : U R s.center ≤ S := (U_le_Z R s.center).trans (Z_le_stabilizer R s.center)
  have hnatural : Nat.card (⁅(U R s.center).subgroupOf S, J⁆ : Subgroup S) = 4 := by
    rw [← card_map_of_injective (f := S.subtype) S.subtype_injective,
      map_commutator, map_subgroupOf_eq_of_le hUS, map_subgroupOf_eq_of_le hJS]
    exact w.natural_commutator_card common hb
  exact Moving.fixed_quotient_card_eq_two s.frame.naturalU
    (spanDual source (s.center_color (by omega)) (s.center_distance (by omega))
      (by omega) s.frame s.opposite) J (IsElementaryAbelian.isPGroup 2 J) hnatural

include w in
/-- The radius/kernel intersection maps into the opposite fixed subgroup, giving the source lower index. -/
theorem span_endpoint_index_ge_four (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    4 ≤ (Q R s.endpoint).relIndex (localZSpan R s.start s.center) := by
  let S := stabilizer R s.center
  let := finite_stabilizer R s.center
  let W := (localZSpan R s.start s.center).subgroupOf S
  let Uc := (U R s.center).subgroupOf S
  let N := (B R s.center (geometry.Z_normal s.center)).subgroupOf S
  let J := (s.continuationSpan w).subgroupOf S
  let Y := (Q R s.endpoint).subgroupOf S
  let := fixed_normal (geometry := geometry) s.center
  have hWS : localZSpan R s.start s.center ≤ S := s.frame.sectionData.local_group
  have hUS : U R s.center ≤ S := (U_le_Z R s.center).trans (Z_le_stabilizer R s.center)
  have hJS : s.continuationSpan w ≤ S := w.span_le_center_stabilizer (by omega)
  have hnatural : Nat.card (⁅Uc, J⁆ : Subgroup S) = 4 := by
    rw [← card_map_of_injective (f := S.subtype) S.subtype_injective,
      map_commutator, map_subgroupOf_eq_of_le hUS, map_subgroupOf_eq_of_le hJS]
    exact w.natural_commutator_card common hb
  have hi := Moving.fixed_index_ge_four s.frame.naturalU
    (spanDual source (s.center_color (by omega)) (s.center_distance (by omega))
      (by omega) s.frame s.opposite) J hnatural
  have hZB : Z R s.center ≤ B R s.center (geometry.Z_normal s.center) := by
    have hVS : V R s.center ≤ S :=
      (geometry.V_le_Q (by omega) s.center (s.center_color (by omega))).trans (fun _ hx => hx.1)
    intro x hx
    apply (mem_B_iff R s.center (geometry.Z_normal s.center) hVS x).mpr
    refine ⟨Z_le_VBall R s.center 2 hx, ?_⟩
    intro l hl
    exact (le_normalizer_iff_commutator_le_right.mp
      ((Ltilde_le_stabilizer s.center).trans (Z_normalized R s.center)))
        (commutator_mem_commutator hl hx)
  have hbound : ⁅W ⊓ Y, J⁆ ≤ N := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hJS]
    have hle : (W ⊓ Y).map S.subtype ≤ V R s.center ⊓ Q R s.endpoint := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨localZSpan_le_V R (s.center_distance (by omega)).le hx.1, hx.2⟩
    exact (commutator_mono hle le_rfl).trans ((w.radius_commutator common hb).trans
      ((w.endpointSpan_le_center_Z common hb).trans hZB))
  have hfixed : W ⊓ Y ≤ centralizerModulo W J N := by
    intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hx.1, ?_⟩
    intro j hj
    rw [commutator_comm] at hbound
    exact hbound (commutator_mem_commutator hj hx)
  have hmono := relIndex_le_of_le_left hfixed
    (show (W ⊓ Y).relIndex W ≠ 0 from ((W ⊓ Y).subgroupOf W).index_ne_zero_of_finite)
  have hh := hi.trans hmono
  rwa [inf_relIndex_left, relIndex_subgroupOf hWS] at hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
