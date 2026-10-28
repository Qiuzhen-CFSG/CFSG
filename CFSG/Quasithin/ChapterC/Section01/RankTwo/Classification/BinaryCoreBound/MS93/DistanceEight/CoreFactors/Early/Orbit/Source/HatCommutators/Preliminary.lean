module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Preliminary.NaturalAction

/-!
# The source reduction of the preliminary hat displacement

The actual relative normalizer preserves Z_a Z_c, even though its elements
need not fix the incident vertex t. The edge index and moving-neighbor
condition identify Z_a Z_c / Z_a as a binary line. Centrality identifies
the radical denominator of Earlier.natural_section with Z_a. The supplied
hat identity embeds the first hat in its marked natural moving section.

The finite natural-line calculation puts displacement by the entire incident
kernel in Z_a Z_c. Inclusion of the neighboring kernel then constructs all
four required path estimates. Only the supplied first-hat identity remains
explicit; no sharpened commutator estimate or orbit-control record is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.2)--(4.5.3), pp.897--898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
open PathCentrality NormalizerTransfer
universe u

variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem radius_commutator_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (ha : color R a = false) :
    ⁅V R a, Q R a⁆ ≤ Z R a := by
  let := V_elementary_of_four_lt R ha (by rw [earlier.distance]; decide)
  have hVQ := V_le_Q R ha common.large_distance
  have hcommV : ⁅V R a, Q R a⁆ ≤ V R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (DistanceEight.V_normalized R a))
  rw [← common.X_eq_Z a ha]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  refine ⟨hVQ (hcommV hx), elemPow_eq_one_of_isElementaryAbelian x (hcommV hx), ?_⟩
  obtain ⟨z, hz, rfl⟩ := earlier.centrality a ha hx
  intro q hq
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨q, hq.1⟩)

private theorem inf_eq_of_index_two {G : Type*} [Group G] {A B E : Subgroup G}
    (hEA : E ≤ A) (hEB : E ≤ B) (hi : E.relIndex A = 2) (hn : ¬ A ≤ B) :
    A ⊓ B = E := by
  have hEI : E ≤ A ⊓ B := le_inf hEA hEB
  have hiI := relIndex_mul_relIndex E (A ⊓ B) A hEI inf_le_left
  rw [hi] at hiI
  have hdiv : (A ⊓ B).relIndex A ∣ 2 :=
    ⟨E.relIndex (A ⊓ B), by rw [mul_comm]; exact hiI.symm⟩
  have htwo : (A ⊓ B).relIndex A = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdiv with h | h
    · exact (hn ((relIndex_eq_one.mp h).trans inf_le_right)).elim
    · exact h
  rw [htwo] at hiI
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hEI

/-- The actual neighbor product is a binary line over the local Z-layer. -/
theorem neighbor_product_relIndex (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : c ∈ Escape.movingNeighbors geometry a) :
    (Z R a).relIndex (Z R a ⊔ Z R c) = 2 := by
  let S := stabilizer R a
  have hcS : Z R c ≤ S :=
    ((le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm]; exact hmove.1.le) le_rfl) :
      Z R c ≤ V R a).trans (V_le_Q R ha common.large_distance)).trans (fun _ hx => hx.1)
  have hinf : Z R c ⊓ Z R a = Z R t := inf_eq_of_index_two
    (Escape.EdgeTransfer.edge_Z_le c t hc hct)
    (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index c t hc hct)
    (fun h => hmove.2 (h.trans (Escape.EdgeTransfer.Z_le_B common.large_distance a ha)))
  let : ((Z R a).subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer (Z_normalized R a)
  have h : ((Z R a).subgroupOf S).relIndex
      ((Z R a).subgroupOf S ⊔ (Z R c).subgroupOf S) = 2 := by
    rw [relIndex_sup_left, relIndex_subgroupOf hcS, ← inf_relIndex_left,
      hinf, earlier.edge_Z_index c t hc hct]
  rw [← subgroupOf_sup (Z_le_stabilizer R a) hcS,
    relIndex_subgroupOf (sup_le (Z_le_stabilizer R a) hcS)] at h
  exact h

/-- The relative normalizer preserves both factors, without fixing the edge vertex. -/
theorem neighbor_product_normalized (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : c ∈ Escape.movingNeighbors geometry a) :
    relativeNormalizer R a t ≤ normalizer (Z R a ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
  exact (le_inf (inf_le_left.trans (Z_normalized R a))
    (Z_normalized_by_relativeNormalizer_of_moving common earlier hc ha hct hat hmove)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Local application of the natural-line calculation to the original section. -/
theorem displacement_of_naturalLineAction (action : NaturalLineAction.{u})
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : c ∈ Escape.movingNeighbors geometry a)
    (identity : hatV R a c = Vcirc R a ⊔ Z R a) :
    ⁅hatV R a c, Q R t⁆ ≤ Z R a ⊔ Z R c := by
  obtain ⟨s⟩ := earlier.natural_section a ha
  let S := stabilizer R a
  let := finite_stabilizer R a
  let H₀ := (V R a).subgroupOf S
  let N₀ := (Z R a).subgroupOf S
  let Q₀ := (Q R a).subgroupOf S
  let D := Escape.radicalPreimage Q₀ H₀ N₀
  let F := Escape.movingPreimage Q₀ H₀ N₀
  let P := (relativeNormalizer R a t).subgroupOf S
  let T := (Q R t).subgroupOf S
  let E := (Z R a ⊔ Z R c).subgroupOf S
  have hZ : N₀.map S.subtype = Z R a :=
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)
  have hH : H₀.map S.subtype = V R a := map_subgroupOf_eq_of_le s.local_group
  have hQ : Q₀.map S.subtype = Q R a := map_subgroupOf_eq_of_le (fun _ hx => hx.1)
  have hDmap : D.map S.subtype = Z R a := by
    change (N₀ ⊔ ⁅H₀, Q₀⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hZ, hH, hQ]
    exact sup_eq_left.mpr (radius_commutator_le_Z common earlier ha)
  have hD : D = N₀ := map_injective S.subtype_injective (hDmap.trans hZ.symm)
  have hF : F.map S.subtype = Z R a ⊔ ⁅V R a, S⁆ := by
    change (D ⊔ ⁅H₀, (⊤ : Subgroup S)⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hDmap, hH, ← MonoidHom.range_eq_map, S.range_subtype]
  have hhat : hatV R a c ≤ F.map S.subtype := by
    rw [identity, hF]
    exact sup_le ((commutator_mono le_rfl (Ltilde_le_stabilizer _)).trans le_sup_right)
      le_sup_left
  have hline : Z R a ⊔ Z R c ≤ hatV R a c := by
    refine sup_le ?_ (Z_le_localZSpan R c a)
    rw [identity]
    exact le_sup_right
  have hlineS : Z R a ⊔ Z R c ≤ S :=
    (hline.trans (hatV_le_radius R (by rw [SimpleGraph.dist_comm]; exact hmove.1.le))).trans s.local_group
  have hE : E.map S.subtype = Z R a ⊔ Z R c := map_subgroupOf_eq_of_le hlineS
  have hn : RankOnePairing.NaturalFactor s.projection ⊤ F N₀ := by
    have n := s.module_section.natural
    change RankOnePairing.NaturalFactor s.projection ⊤ F D at n
    rwa [hD] at n
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQtS : Q R t ≤ S := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hT : T.map S.subtype = Q R t := map_subgroupOf_eq_of_le hQtS
  have hQP : Q₀ ≤ P := by
    intro x hx
    exact ⟨x.property, (Q R t).le_normalizer (Q_le_adjacent_h R ht hat hx)⟩
  have hPN : P ≤ normalizer E := by
    intro g hg
    rw [← subgroupOf_normalizer_eq hlineS]
    exact neighbor_product_normalized common earlier ha hc hat hct hmove hg
  have hTP : T ≤ P := fun x hx => ⟨x.property, (Q R t).le_normalizer hx⟩
  have hPT : P ≤ normalizer T := by
    intro g hg
    rw [← subgroupOf_normalizer_eq hQtS]
    exact hg.2
  have hEF : E ≤ F := by
    intro x hx
    have hm : (x : FreeAmalgam R) ∈ F.map S.subtype := hhat (hline hx)
    obtain ⟨y, hy, he⟩ := hm
    exact (Subtype.ext he : y = x) ▸ hy
  have hindex : N₀.relIndex E = 2 := by
    rw [relIndex_subgroupOf hlineS]
    exact neighbor_product_relIndex common earlier ha hc hat hct hmove
  have hcomm : ⁅F, T⁆ ≤ E := action S s.projection F N₀ P T E
    s.module_section.projection_surjective
    (s.module_section.projection_kernel ▸ hQP)
    (relativeNormalizer_isCoatom common earlier ha hat) hn
    (subgroupOf_mono S le_sup_left) hEF hindex hPN hTP hPT
    (ModuleAlternatives.kernel_isPGroup source t).comap_subtype
  have hm := map_mono (f := S.subtype) hcomm
  rw [map_commutator, hT, hE] at hm
  exact (commutator_mono hhat le_rfl).trans hm

/-- All four literal displacement estimates, conditional only on the finite natural-line lemma. -/
theorem preliminaryOnPath_of_naturalLineAction (action : NaturalLineAction.{u})
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p) :
    PreliminaryOnPath p := by
  constructor
  intro i hi hi4 hi10
  have hc := hi.add (by decide : Even 2)
  have ha := p.even_color hi (by omega)
  have hct : Adjacent R (p.walk.getVert (i + 2)) (p.walk.getVert (i + 1)) :=
    adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  have ht : color R (p.walk.getVert (i + 1)) = true := by
    have hne := adjacent_color_ne R (p.adjacent (i := i) (by omega))
    cases h : color R (p.walk.getVert (i + 1)) <;> simp_all
  exact (commutator_mono le_rfl (Q_le_adjacent_h R ht hct)).trans
    (displacement_of_naturalLineAction action common earlier ha (p.even_color hc (by omega))
      (p.adjacent (by omega)) hct
      (p.moving_neighbors source common earlier hi (by omega) (by omega)).2
      (identity.forward i hi (by omega) (by omega)))

/-- The preliminary p.898 displacement at the four centers of the supplied path.
The actual preceding section and relative-normalizer action discharge all
module premises; the first-hat identities are the sole explicit source step. -/
theorem preliminaryOnPath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (identity : HatIdentitiesOnPath R p) : PreliminaryOnPath p :=
  preliminaryOnPath_of_naturalLineAction naturalLineAction common earlier p identity

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
