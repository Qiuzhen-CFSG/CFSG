module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.SelectionGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Dimension

/-!
# The endpoint image bound and saturation

For b > 4 the center radius group is elementary abelian and lies in the endpoint
stabilizer. Its image in the actual endpoint SL3(2) quotient has order at most
four. The quotient kernel is precisely Q_b, so [V_c : V_c intersect Q_b] <= 4.

An opposite-quotient lower bound [W : W intersect Q_b] >= 4 forces W and
V_c intersect Q_b to generate V_c. The proof works inside the finite elementary
radius group; it does not assert finiteness of the free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable (s : SelectedPath R geometry a c)

open Escape.Propagation.Backward.Products.Selection.Choices in
/-- The elementary center radius has image of order at most four in the actual endpoint quotient. -/
theorem radius_endpoint_index_le_four (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : (Q R s.endpoint).relIndex (V R s.center) ≤ 4 := by
  have hVS : V R s.center ≤ stabilizer R s.endpoint := by
    apply Escape.Propagation.Backward.Products.V_le_stabilizer_of_dist_add_two_le
      (s.center_color (by omega))
    change (cosetGraph R).dist (s.path.walk.getVert 2) s.endpoint + 2 ≤ geometry.b R
    rw [s.path.dist_end, s.path.length_eq_b]
    omega
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) s.endpoint s.path.end_color
  let H := (V R s.center).subgroupOf (stabilizer R s.endpoint)
  let E := H.map model.projection
  let := V_elementary_of_four_lt R (s.center_color (by omega)) hb
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.subgroupOf hVS
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map model.projection
  have hE : Nat.card E ≤ 4 := by
    by_cases hn : E = ⊥
    · simp [hn]
    have htwo : Representation.BinaryOffender.IsElementaryTwo E := ⟨hn, inferInstance⟩
    rw [htwo.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2)
      (AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two _ inferInstance)
  change Nat.card (H.map model.projection) ≤ 4 at hE
  rwa [← relIndex_ker, model.kernel, relIndex_subgroupOf hVS] at hE

/-- Matching endpoint indices force the source saturation V_c = (V_c intersect Q_b) W. -/
theorem radius_eq_kernel_sup_span_of_index (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hspan : 4 ≤ (Q R s.endpoint).relIndex (localZSpan R s.start s.center)) :
    V R s.center = (V R s.center ⊓ Q R s.endpoint) ⊔ localZSpan R s.start s.center := by
  let Vc := V R s.center
  let := finite_stabilizer R s.center
  have hVS : Vc ≤ stabilizer R s.center :=
    (geometry.V_le_Q (by omega) s.center (s.center_color (by omega))).trans (fun _ hx => hx.1)
  let : Finite Vc := Finite.of_injective (inclusion hVS) (inclusion_injective hVS)
  let A := (Q R s.endpoint).subgroupOf Vc
  let W := (localZSpan R s.start s.center).subgroupOf Vc
  have hWV : localZSpan R s.start s.center ≤ Vc :=
    localZSpan_le_V R (s.center_distance (by omega)).le
  let := V_abelian_of_four_lt R (s.center_color (by omega)) hb
  have hupper : A.index ≤ 4 := s.radius_endpoint_index_le_four common hb
  have hlower : 4 ≤ A.relIndex W := by
    rwa [relIndex_subgroupOf hWV]
  have he := relIndex_sup_left W A
  have hm := relIndex_mul_index (show A ≤ A ⊔ W from le_sup_left)
  rw [he] at hm
  have hpos : 0 < (A ⊔ W).index := Nat.pos_of_ne_zero (A ⊔ W).index_ne_zero_of_finite
  have hi : (A ⊔ W).index = 1 := by nlinarith
  have ht := index_eq_one.mp hi
  have heq := congrArg (map Vc.subtype) ht
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hWV, ← MonoidHom.range_eq_map,
    range_subtype] at heq
  change ((Q R s.endpoint).subgroupOf Vc).map Vc.subtype ⊔ _ = _ at heq
  rw [subgroupOf_map_subtype, inf_comm] at heq
  exact heq.symm
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
