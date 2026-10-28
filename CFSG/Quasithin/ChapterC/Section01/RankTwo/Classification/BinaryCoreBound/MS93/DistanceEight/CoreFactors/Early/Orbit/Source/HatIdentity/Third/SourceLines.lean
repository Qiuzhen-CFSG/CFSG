module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.LineModel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.RelativeKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation

/-!
# Original marked quotient lines and the neighboring parabolic obstruction

The natural section at a genuine source vertex supplies literal coordinates
on V/Z. Moving critical Z-layers become binary quotient lines. Their
relative normalizers are the corresponding line parabolics, while the
incident edge kernel is the full two-core. Thus a commutator contained in the
source fixed preimage would force two distinct edge parabolics to coincide,
which is impossible on the original path.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.898,
using the natural section in (4.3.1) and the marked line geometry preceding
(4.3.7). All maps and kernels here are the supplied original source maps.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.SourceLines
open PathCentrality NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
open LineModel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

noncomputable def lineFactor (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :=
  Escape.PairingControl.FirstPairing.Orientation.ImageCases.natural_coordinates_at (geometry := geometry)
    source (by have := common.large_distance; omega) hc s
noncomputable def actor (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) : stabilizer R c →* SL :=
  (lineFactor common hc s).marking.toMonoidHom.comp s.projection
noncomputable def image (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) (a : Vertex R) : Subgroup Space :=
  coordinateImage (lineFactor common hc s) ((Z R a).subgroupOf (stabilizer R c))

theorem actor_surjective (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    Function.Surjective (actor common hc s) :=
  (lineFactor common hc s).marking.surjective.comp s.module_section.projection_surjective

theorem actor_kernel (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    (actor common hc s).ker = (Q R c).subgroupOf (stabilizer R c) := by
  rw [actor, MonoidHom.ker_comp_of_injective _ _ (lineFactor common hc s).marking.injective,
    s.module_section.projection_kernel]

omit [Finite M] in
private theorem Z_le_radius {a c : Vertex R}
    (hm : a ∈ Escape.movingNeighbors geometry c) : Z R a ≤ V R c :=
  le_iSup_of_le a (le_iSup_of_le (by rw [SimpleGraph.dist_comm]; exact hm.1.le) le_rfl)

theorem image_card (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hm : a ∈ Escape.movingNeighbors geometry c)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    Nat.card (image common hc s a) = 2 := by
  rw [image,coordinateImage_card _ _ (subgroupOf_mono _ (Z_le_radius hm)),
    relIndex_subgroupOf ((Z_le_radius hm).trans s.local_group),
    ← inf_relIndex_left, moving_Z_inf_B common earlier ha hc hat hct hm,
    earlier.edge_Z_index a t ha hat]

theorem parabolic_image (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hm : a ∈ Escape.movingNeighbors geometry c)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    ((relativeNormalizer R c t).subgroupOf (stabilizer R c)).map (actor common hc s) =
      planeStabilizer (image common hc s a) := by
  apply coordinateImage_stabilizer (lineFactor common hc s) s.module_section.projection_surjective
    _ _ (relativeNormalizer_isCoatom common earlier hc hct)
  · intro g hg
    rw [← subgroupOf_normalizer_eq ((Z_le_radius hm).trans s.local_group)]
    exact Z_normalized_by_relativeNormalizer_of_moving common earlier ha hc hat hct hm hg
  · exact image_card common earlier ha hc hat hct hm s

theorem edge_kernel_image (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hm : a ∈ Escape.movingNeighbors geometry c)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    ((Q R t).subgroupOf (stabilizer R c)).map (actor common hc s) =
      (planeStabilizer (image common hc s a)).pCoreIn 2 := by
  let := finite_stabilizer R c
  have hk : IsPGroup 2 (actor common hc s).ker := by
    rw [actor_kernel]
    exact (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
  rw [← Neighbor.relativeNormalizer_core common earlier hc hct,
    map_pCoreIn_of_ker_isPGroup _ hk,
    parabolic_image common earlier ha hc hat hct hm s]

private theorem kernel_le_parabolic (common : CommonFacts R source geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    (actor common hc s).ker ≤ (relativeNormalizer R c t).subgroupOf (stabilizer R c) := by
  rw [actor_kernel]
  have ht : color R t = true := by
    have h := adjacent_color_ne R hct
    cases h' : color R t <;> simp_all
  intro x hx
  exact ⟨hx.1, (Q R t).le_normalizer (Q_le_adjacent_h R ht hct hx)⟩

/-- The other moving neighbor's quotient line cannot be fixed by the
opposite incident kernel; all parabolic and module markings are original. -/
theorem not_neighbor_commutator_le_B (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d u v : Vertex R}
    (ha : color R a = false) (hc : color R c = false) (hd : color R d = false)
    (hau : Adjacent R a u) (hcu : Adjacent R c u)
    (hdv : Adjacent R d v) (hcv : Adjacent R c v)
    (hma : a ∈ Escape.movingNeighbors geometry c)
    (hmd : d ∈ Escape.movingNeighbors geometry c)
    (hne : Z R u ≠ Z R v)
    (s : Escape.NaturalSectionAt c (V R c) (Z R c)) :
    ¬ ⁅Z R d, Q R u⁆ ≤ B R c (geometry.Z_normal c) := by
  intro hcomm
  let S := stabilizer R c
  have hZd := (Z_le_radius hmd).trans s.local_group
  have hQu : Q R u ≤ S := fun _ hx => hx.2 c (adjacent_symm R hcu)
  have hcomm' : ⁅(Z R d).subgroupOf S, (Q R u).subgroupOf S⁆ ≤
      (B R c (geometry.Z_normal c)).subgroupOf S := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hZd,map_subgroupOf_eq_of_le hQu]
    exact hcomm
  have hfix := coordinateImage_fixed_of_commutator (lineFactor common hc s)
    ((Z R d).subgroupOf S) ((Q R u).subgroupOf S) hcomm'
  change image common hc s d ≤ fixedSpace (((Q R u).subgroupOf S).map (actor common hc s)) at hfix
  rw [edge_kernel_image common earlier ha hc hau hcu hma s,
    fixed_core_line _ (image_card common earlier ha hc hau hcu hma s)] at hfix
  have he : image common hc s d = image common hc s a :=
    eq_of_le_of_card_ge hfix (by rw [image_card common earlier ha hc hau hcu hma s,
      image_card common earlier hd hc hdv hcv hmd s])
  have hm : ((relativeNormalizer R c u).subgroupOf S).map (actor common hc s) =
      ((relativeNormalizer R c v).subgroupOf S).map (actor common hc s) := by
    rw [parabolic_image common earlier ha hc hau hcu hma s,
      parabolic_image common earlier hd hc hdv hcv hmd s,he]
  have hP := map_injective_of_ker_le (actor common hc s)
    (kernel_le_parabolic common hc hcu s) (kernel_le_parabolic common hc hcv s) hm
  have heq := congrArg (Subgroup.map S.subtype) hP
  rw [map_subgroupOf_eq_of_le (show relativeNormalizer R c u ≤ S from inf_le_left),
    map_subgroupOf_eq_of_le (show relativeNormalizer R c v ≤ S from inf_le_left)] at heq
  exact Neighbor.relativeNormalizer_ne_of_edge_Z_ne common earlier hc hcu hcv hne heq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.SourceLines
