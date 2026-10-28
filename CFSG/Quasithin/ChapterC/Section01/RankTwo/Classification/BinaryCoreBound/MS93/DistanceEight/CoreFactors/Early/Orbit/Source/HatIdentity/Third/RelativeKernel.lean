module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Neighbor
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
public import Theory.GroupTheory.PCoreImage

/-!
# Intrinsic edge kernels and distinct relative parabolics

The actual natural eight-group identifies each edge image with a pointwise
plane fixer. Its matrix normalizer has that fixer as its full two-core.
Lifting through the original two-group kernel identifies the intrinsic core
of the relative normalizer with the actual incident edge kernel. Distinct
edge Z-layers consequently give distinct relative parabolics, including the
literal two parabolics at every interior vertex of the source path.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5.3), pp.894--898.
These are the marked parabolic inputs to the remaining natural-module step.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Neighbor
open PathCentrality NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
open FiniteGeometry
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem plane_core (A : Subgroup Space) (hA : Nat.card A = 4) :
    (planeStabilizer A).pCoreIn 2 = planeFixer A := by
  obtain ⟨g, rfl⟩ := plane_transitive A hA
  rw [planeStabilizer_move, planeFixer_move, standardPlane_stabilizer,
    standardPlane_fixer, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    Matrix.PSL3Two.lineParabolicSL_pCoreIn_two_eq_R]

private theorem edge_actor_image (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (model : LocalModel a) :
    model.actorImage (Q R t) = planeFixer (model.coordinates ⁅Z R a, Q R t⁆) := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hE : ⁅Z R a, Q R t⁆ ≤ Z R t :=
    commutator_le_of_normalized_index_two _ _ _
      (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index a t ha hat)
      (hloc.trans (Z_normalized R a))
      ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))
  have hfix : ⁅Z R a, Q R t⁆ ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
      (LocalCommutator.moduleFacts common) a t ha hat] at hE
    exact hE.trans inf_le_right
  have hEU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) a t ha hat
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
    exact (model.action_fixed_iff g u).mpr (hfix hu g hg)
  · rw [model.actorImage_card _ hloc, earlier.edge_Q_index a t ha hat,
      FiniteGeometry.planeFixer_card _ (by
        rw [model.coordinates_card _ hEU, First.Layer.edge_displacement_card common earlier ha hat])]

/-- The relative normalizer has the actual edge kernel as its two-core. -/
theorem relativeNormalizer_core (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    ((relativeNormalizer R a t).subgroupOf (stabilizer R a)).pCoreIn 2 =
      (Q R t).subgroupOf (stabilizer R a) := by
  obtain ⟨model⟩ := localModel_nonempty source (LocalCommutator.moduleFacts common) a ha
  let S := stabilizer R a
  let := finite_stabilizer R a
  let N := (relativeNormalizer R a t).subgroupOf S
  let A := model.coordinates ⁅Z R a, Q R t⁆
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQt : Q R t ≤ S := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQQ := Q_le_adjacent_h R ht hat
  have hA : Nat.card A = 4 := by
    rw [model.coordinates_card _ (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) a t ha hat), First.Layer.edge_displacement_card common earlier ha hat]
  have hpre := model.actorImage_comap (Q R t) hQQ
  rw [edge_actor_image common earlier ha hat model] at hpre
  have hNpre : (planeStabilizer A).comap model.projection = N := by
    rw [← planeFixer_normalizer A hA,
      comap_normalizer_eq_of_surjective _ model.surjective, hpre,
      ← subgroupOf_normalizer_eq hQt]
    simp only [N, relativeNormalizer, S, inf_subgroupOf_left]
  have hNmap : N.map model.projection = planeStabilizer A := by
    rw [← hNpre, map_comap_eq_self_of_surjective model.surjective]
  have hk : IsPGroup 2 model.projection.ker := by
    rw [model.kernel]
    exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  have hcoremap : (N.pCoreIn 2).map model.projection = planeFixer A := by
    rw [map_pCoreIn_of_ker_isPGroup model.projection hk N, hNmap, plane_core A hA]
  have hkernel : model.projection.ker ≤ N.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hk
    · rw [← hNpre]
      exact ker_le_comap _ _
    · exact le_normalizer_of_normal
  apply map_injective_of_ker_le model.projection hkernel
    (by rw [model.kernel]; exact subgroupOf_mono S hQQ)
  rw [hcoremap]
  exact (edge_actor_image common earlier ha hat model).symm

/-- Distinct edge Z-layers have distinct actual relative normalizers. -/
theorem relativeNormalizer_ne_of_edge_Z_ne (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a s t : Vertex R} (ha : color R a = false)
    (has : Adjacent R a s) (hat : Adjacent R a t) (hne : Z R s ≠ Z R t) :
    relativeNormalizer R a s ≠ relativeNormalizer R a t := by
  intro hh
  have hc := congrArg (fun N : Subgroup (FreeAmalgam R) =>
    (N.subgroupOf (stabilizer R a)).pCoreIn 2) hh
  rw [relativeNormalizer_core common earlier ha has,
    relativeNormalizer_core common earlier ha hat] at hc
  have hqs := congrArg (Subgroup.map (stabilizer R a).subtype) hc
  rw [map_subgroupOf_eq_of_le (show Q R s ≤ stabilizer R a from
      fun _ hx => hx.2 a (adjacent_symm R has)),
    map_subgroupOf_eq_of_le (show Q R t ≤ stabilizer R a from
      fun _ hx => hx.2 a (adjacent_symm R hat))] at hqs
  apply hne
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (LocalCommutator.moduleFacts common) a s ha has,
    Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (LocalCommutator.moduleFacts common) a t ha hat,
    hqs]

/-- Distinct actual backward and forward parabolics at an interior path vertex. -/
theorem source_relativeNormalizers_ne (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1)) ≠
      relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1)) := by
  apply relativeNormalizer_ne_of_edge_Z_ne common earlier (p.even_color hi (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  · exact p.adjacent (by omega)
  · exact p.edge_Z_ne i hi hi2 hi12

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.Neighbor
