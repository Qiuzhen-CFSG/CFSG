module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# Corrected source generation in MS93 (4.5.2)(ii)

The natural model identifies the relative normalizer of Q_t with the inverse
image of a maximal plane stabilizer. If the critical endpoint lay in that
normalizer, (4.5.2)(i) would make it normalize the preceding Z-layer. That
layer has index two over the incident edge layer. Its action is therefore
trivial modulo Z_a and hence modulo B_a. The actual quotient-centralizer
identity of (4.5.1)(iii) then contradicts the preceding critical window.

This proves subgroup generation and the literal ordered setwise product
with C_a. All three forward and three reflected instances retain the given
walk. The final producers construct FirstFactsOnPath from the published
first-calculation theorem; no selected normality or generation is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.2)(ii), printed p.897;
relative-normalizer notation on p.881 and the first calculations on p.896.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
open PathCentrality
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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

/-- The actual relative kernel normalizer is maximal in its finite local group. -/
theorem relativeNormalizer_isCoatom (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    IsCoatom ((relativeNormalizer R a t).subgroupOf (stabilizer R a)) := by
  obtain ⟨model⟩ := localModel_nonempty source (LocalCommutator.moduleFacts common) a ha
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hpre := model.actorImage_comap (Q R t) (Q_le_adjacent_h R ht hat)
  have hE := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) a t ha hat
  have hcard : Nat.card (model.coordinates ⁅Z R a, Q R t⁆) = 4 := by
    rw [model.coordinates_card _ hE, First.Layer.edge_displacement_card common earlier ha hat]
  rw [edge_actor_image common earlier ha hat model] at hpre
  have he : (planeStabilizer (model.coordinates ⁅Z R a, Q R t⁆)).comap model.projection =
      (relativeNormalizer R a t).subgroupOf (stabilizer R a) := by
    rw [← FiniteGeometry.planeFixer_normalizer _ hcard,
      comap_normalizer_eq_of_surjective _ model.surjective, hpre,
      ← subgroupOf_normalizer_eq
        (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat))]
    simp only [relativeNormalizer, inf_subgroupOf_left]
  rw [← he]
  exact Subgroup.isCoatom_comap_of_surjective model.surjective
    (FiniteGeometry.planeStabilizer_isCoatom _ hcard)

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

private theorem endpoint_not_normalizes_previous
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b c d e f s t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hZaQe : Z R a ≤ Q R e) (hZbV : Z R b ≤ V R a)
    (hZfG : Z R f ≤ stabilizer R a) (hn : ¬ Z R b ≤ Q R e)
    (first : FirstFacts R geometry a c d e f s) :
    ¬ Z R f ≤ normalizer (Z R b : Set (FreeAmalgam R)) := by
  intro hnorm
  have hinf : Z R b ⊓ Z R a = Z R t :=
    inf_eq_of_index_two (Escape.EdgeTransfer.edge_Z_le b t hb hbt)
      (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index b t hb hbt)
      (fun h => hn (h.trans hZaQe))
  have hNt : Z R f ≤ normalizer (Z R t : Set (FreeAmalgam R)) := by
    rw [← hinf]
    exact (le_inf hnorm (hZfG.trans (Z_normalized R a))).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Z R b, Z R f⁆ ≤ B R a (geometry.Z_normal a) :=
    (commutator_le_of_normalized_index_two _ _ _
      (Escape.EdgeTransfer.edge_Z_le b t hb hbt) (earlier.edge_Z_index b t hb hbt)
      hnorm hNt).trans
      ((Escape.EdgeTransfer.edge_Z_le a t ha hat).trans
        (Escape.EdgeTransfer.Z_le_B common.large_distance a ha))
  let S := stabilizer R a
  let B₀ := (B R a (geometry.Z_normal a)).subgroupOf S
  let : B₀.Normal := first.B_normal
  let π := QuotientGroup.mk' B₀
  let A := (V R a ⊓ Q R e).subgroupOf S
  have hBA : π.ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact ⟨Escape.EdgeTransfer.B_le_radius common.large_distance a ha hx, first.B_le hx⟩
  have heq : (A.map π).comap π = A := comap_map_eq_self hBA
  apply hn
  intro x hx
  have hxG : x ∈ S := (hZbV.trans
    ((V_le_Q R ha common.large_distance).trans (fun _ hy => hy.1))) hx
  have hcq : π ⟨x, hxG⟩ ∈
      centralizer (((Z R f).subgroupOf S).map π : Set (S ⧸ B₀)) := by
    have hc' : (⟨x, hxG⟩ : S) ∈ centralizerModulo ⊤ ((Z R f).subgroupOf S) B₀ := by
      apply mem_centralizerModulo_iff.mpr
      refine ⟨mem_top _, ?_⟩
      intro z hz
      exact hcomm (by rw [commutator_comm]; exact commutator_mem_commutator hz hx)
    exact hc'.2
  have hxq : π ⟨x, hxG⟩ ∈ A.map π := by
    rw [first.quotient_centralizer]
    exact ⟨mem_map_of_mem π (hZbV hx), hcq⟩
  have hxa : (⟨x, hxG⟩ : S) ∈ A := heq ▸ hxq
  exact hxa.2

/-- The printed generation implication, using exactly the preceding moving and critical window. -/
theorem generation_of_first_window
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b c d e f s t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : b ∈ Escape.movingNeighbors geometry a)
    (hZaQe : Z R a ≤ Q R e) (hZbV : Z R b ≤ V R a)
    (hZfG : Z R f ≤ stabilizer R a) (hn : ¬ Z R b ≤ Q R e)
    (first : FirstFacts R geometry a c d e f s) :
    relativeNormalizer R a t ⊔ Z R f = stabilizer R a := by
  let P := relativeNormalizer R a t
  let S := stabilizer R a
  have hnP : ¬ Z R f ≤ P := fun h =>
    endpoint_not_normalizes_previous common earlier ha hb hat hbt hZaQe hZbV hZfG hn first
      (h.trans (Z_normalized_by_relativeNormalizer_of_moving common earlier hb ha hbt hat hmove))
  have hnot : ¬ (Z R f).subgroupOf S ≤ P.subgroupOf S := by
    intro h
    apply hnP
    intro x hx
    exact h (show (⟨x, hZfG hx⟩ : S) ∈ (Z R f).subgroupOf S from hx)
  have he : P.subgroupOf S ⊔ (Z R f).subgroupOf S = ⊤ :=
    (relativeNormalizer_isCoatom common earlier ha hat).2 _ (left_lt_sup.mpr hnot)
  have hh := congrArg (Subgroup.map S.subtype) he
  have hZG : Z R f ≤ S := hZfG
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (show P ≤ S from inf_le_left),
    map_subgroupOf_eq_of_le hZG, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite M] in
private theorem path_Z_le_Q {a : Vertex R} (earlier : Earlier R geometry)
    (p : SourcePath R a) {i j : ℕ} (hi : Even i)
    (hi14 : i ≤ 14) (hj14 : j ≤ 14) (hij : (i - j) + (j - i) < 8) :
    Z R (p.walk.getVert i) ≤ Q R (p.walk.getVert j) := by
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hi hi14))
  rw [geometry.distance_constant _ (p.even_color hi hi14)]
  change _ < geometry.b R
  rw [earlier.distance]
  rcases le_total i j with h | h
  · rw [p.distance (geometry := geometry) h hj14]
    omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) h hi14]
    omega

/-- Subgroup generation at all three forward first-calculation centers of this path. -/
theorem forward_generation (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (first : FirstFactsOnPath R geometry p) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi6 : i ≤ 6) :
    relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1)) ⊔
      Z R (p.walk.getVert (i + 8)) = stabilizer R (p.walk.getVert i) := by
  have hb : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  apply generation_of_first_window common earlier
    (p.even_color hi (by omega)) (p.even_color hb (by omega))
    (t := p.walk.getVert (i - 1))
    (e := p.walk.getVert (i + 6)) (first := first.forward i hi hi2 hi6)
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using p.adjacent (i := i - 2) (by omega)
  · exact (p.moving_neighbors source common earlier hi hi2 (by omega)).1
  · exact path_Z_le_Q earlier p hi (by omega) (by omega) (by omega)
  · exact le_iSup_of_le _ (le_iSup_of_le
      (show (cosetGraph R).dist (p.walk.getVert (i - 2)) (p.walk.getVert i) ≤ 2 by
        rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega) le_rfl)
  · exact (source.critical_Z_le_stabilizer geometry _ (p.even_color hi (by omega)) _
      (p.critical_pair earlier hi hi6)).2
  · simpa only [show i - 2 + 8 = i + 6 by omega] using (p.critical (i - 2) hb (by omega)).2

/-- Subgroup generation at all three reflected centers, without selecting a new path. -/
theorem backward_generation (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    (first : FirstFactsOnPath R geometry p) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1)) ⊔
      Z R (p.walk.getVert (i - 8)) = stabilizer R (p.walk.getVert i) := by
  have hb : Even (i + 2) := hi.add (by decide)
  apply generation_of_first_window common earlier
    (p.even_color hi (by omega)) (p.even_color hb (by omega))
    (t := p.walk.getVert (i + 1))
    (e := p.walk.getVert (i - 6)) (first := first.backward i hi hi8 hi12)
  · exact p.adjacent (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · exact (p.moving_neighbors source common earlier hi (by omega) hi12).2
  · exact path_Z_le_Q earlier p hi (by omega) (by omega) (by omega)
  · exact le_iSup_of_le _ (le_iSup_of_le
      (show (cosetGraph R).dist (p.walk.getVert (i + 2)) (p.walk.getVert i) ≤ 2 by
        rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega) le_rfl)
  · have he : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
    have hc := p.critical_pair earlier he (by omega)
    rw [Nat.sub_add_cancel hi8] at hc
    exact (source.critical_Z_le_stabilizer geometry _ (p.even_color he (by omega)) _ hc).1
  · have he : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
    have hc := p.critical_pair earlier he (by omega)
    rw [show i - 6 + 8 = i + 2 by omega] at hc
    exact (common.critical_reverse _ (p.even_color he (by omega)) _
      (p.even_color hb (by omega)) hc).2

omit [Finite M] in
private theorem product_eq_of_join {a t f : Vertex R}
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a) :
    (((relativeNormalizer R a t ⊔ Z R f : Subgroup (FreeAmalgam R)) :
      Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R))) =
        (stabilizer R a : Set (FreeAmalgam R)) := by
  rw [hgen]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact (stabilizer R a).mul_mem hx hy.1
  · intro x hx
    exact ⟨x, hx, 1, (C R a).one_mem, mul_one x⟩

/-- Literal (4.5.2)(ii), with subgroup join and the ordered C factor retained. -/
theorem local_generation (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) :
    (((relativeNormalizer R a (p.walk.getVert 3) ⊔ Z R (p.walk.getVert 12) :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R))) =
        (stabilizer R a : Set (FreeAmalgam R)) := by
  apply product_eq_of_join
  simpa only [p.center_eq] using forward_generation common earlier p
    (firstFactsOnPath source common earlier p) (i := 4) (by decide) (by decide) (by decide)

/-- All six ordered source products, with every first-calculation premise discharged. -/
theorem generationOnPath (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) :
    (∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
      (((relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i - 1)) ⊔
        Z R (p.walk.getVert (i + 8)) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) *
          (C R (p.walk.getVert i) : Set (FreeAmalgam R))) =
            (stabilizer R (p.walk.getVert i) : Set (FreeAmalgam R))) ∧
    (∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
      (((relativeNormalizer R (p.walk.getVert i) (p.walk.getVert (i + 1)) ⊔
        Z R (p.walk.getVert (i - 8)) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) *
          (C R (p.walk.getVert i) : Set (FreeAmalgam R))) =
            (stabilizer R (p.walk.getVert i) : Set (FreeAmalgam R))) := by
  have first := firstFactsOnPath source common earlier p
  exact ⟨fun _ hi hi2 hi6 => product_eq_of_join
      (forward_generation common earlier p first hi hi2 hi6),
    fun _ hi hi8 hi12 => product_eq_of_join
      (backward_generation common earlier p first hi hi8 hi12)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
