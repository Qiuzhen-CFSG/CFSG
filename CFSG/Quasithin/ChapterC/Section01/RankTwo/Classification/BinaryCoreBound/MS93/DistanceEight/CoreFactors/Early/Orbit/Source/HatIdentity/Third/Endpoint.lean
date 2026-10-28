module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels.Source

/-!
# Endpoint displacement in the contrary third-containment case

The preceding central plane is in the actual fixed seed. If it centralizes
the critical endpoint, the relative normalizer and that endpoint together
make it an invariant plane of the natural eight-group, which is impossible.
Consequently failure of the ordered product containment forces the entire
last-edge quotient and its four-element displacement. The final application
retains the original SourcePath and constructs its generation inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claim (3), p.898.
This proves the endpoint consequence of failure; the final moving-module
contradiction remains a separate step.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third
open PathCentrality NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The intrinsic natural eight-group has no proper invariant subgroup. -/
theorem natural_subgroup_dichotomy [Finite M]
    (common : CommonFacts R source geometry) {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R a)
    (hn : stabilizer R a ≤ normalizer K) : K = ⊥ ∨ K = U R a := by
  obtain ⟨model⟩ := localModel_nonempty source (LocalCommutator.moduleFacts common) a ha
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z R a).trans (Z_le_stabilizer R a)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor model.projection ⊤ ((U R a).subgroupOf S) ⊥ := {
    marking := MulEquiv.refl _
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized a g.property
    action := by
      intro g _ x y h
      exact congrArg Multiplicative.toAdd (model.action g
        ((subgroupOfEquivOfLe hUS) x) ((subgroupOfEquivOfLe hUS) y)
        (congrArg Subtype.val h)) }
  have hm : (⊤ : Subgroup S).map model.projection = ⊤ :=
    map_top_of_surjective _ model.surjective
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh


/-- The preceding central plane is in the actual fixed seed. -/
theorem H_le_fixedSeed (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {b : Vertex R} (hb : color R b = false) :
    H R b ≤ fixedSeed R b := by
  apply le_inf
  · exact (H_le_Z_of_central common hb (earlier.centrality b hb)).trans (Z_le_VBall R b 2)
  · intro x hx l hl
    obtain ⟨z, hz, rfl⟩ := H_le_localCenter_of_central R b (earlier.centrality b hb) hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, Ltilde_le_stabilizer b hl⟩)

/-- Source generation forces the preceding plane to act at the endpoint. -/
theorem preceding_H_not_le_endpoint [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a) :
    ¬ H R b ≤ Q R f := by
  intro hH
  have hn : stabilizer R a ≤ normalizer (H R b : Set (FreeAmalgam R)) := by
    rw [← hgen]
    apply sup_le (Preliminary.H_normalized_by_relativeNormalizer common earlier ha hb hat hbt hmove)
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R f hf)).trans
      (centralizer_le hH)).trans (Subgroup.centralizer_le_normalizer _)
  rcases natural_subgroup_dichotomy common ha (H R b)
    (Orbit.H_le_neighbor_U common earlier hb hmove) hn with hz | he
  · have hlo := First.Layer.H_card_lower common earlier b hb
    rw [hz, card_bot] at hlo
    omega
  · have hup := H_card_le_four common earlier hb
    rw [he, common.natural.card_at a ha] at hup
    omega

private theorem product_of_small_index {G : Type*} [Group G] {Z K Q : Subgroup G}
    [Finite K] (hZK : Z ≤ K) (hn : ¬ Z ≤ Q) (hi : Q.relIndex K ≤ 2) :
    (K : Set G) ⊆ (Z : Set G) * (Q : Set G) := by
  have hpos : 0 < Q.relIndex K := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := Q.subgroupOf K))
  have hone : Q.relIndex K ≠ 1 := fun h => hn (hZK.trans (relIndex_eq_one.mp h))
  have htwo : Q.relIndex K = 2 := by omega
  obtain ⟨z, hz, hzQ⟩ := SetLike.not_le_iff_exists.mp hn
  intro x hx
  by_cases hxQ : x ∈ Q
  · exact ⟨1, Z.one_mem, x, hxQ, one_mul x⟩
  have hmem : z⁻¹ * x ∈ Q := by
    exact (Q.subgroupOf K).mul_mem_iff_of_index_two htwo
      (a := ⟨z⁻¹, K.inv_mem (hZK hz)⟩) (b := ⟨x, hx⟩) |>.mpr
      (by change z⁻¹ ∈ Q ↔ x ∈ Q; simp only [Q.inv_mem_iff, hzQ, hxQ])
  exact ⟨z, hz, z⁻¹ * x, hmem, mul_inv_cancel_left z x⟩

private theorem product_eq_of_large_image {G : Type*} [Group G]
    {D Q S : Subgroup G} (hD : D ≤ S) (hQ : Q ≤ S)
    (hn : S ≤ normalizer (Q : Set G)) (hi : Q.relIndex S = 4)
    (himage : 2 < Q.relIndex D) :
    (D : Set G) * (Q : Set G) = (S : Set G) := by
  let A := D.subgroupOf S
  let K := Q.subgroupOf S
  let : K.Normal := normal_subgroupOf_of_le_normalizer hn
  have hidx : K.relIndex A = 4 := by
    have hKi : K.index = 4 := hi
    have hdvd : K.relIndex A ∣ 4 := hKi ▸ K.relIndex_dvd_index_of_normal A
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hgt : 2 < K.relIndex A := by rwa [relIndex_subgroupOf hD]
    omega
  have hm := relIndex_mul_index (show K ≤ A ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hidx, show K.index = 4 from hi] at hm
  have he : A ⊔ K = ⊤ := index_eq_one.mp (by omega)
  have hj : D ⊔ Q = S := by
    have hh := congrArg (Subgroup.map S.subtype) he
    simpa only [A, K, Subgroup.map_sup, map_subgroupOf_eq_of_le hD,
      map_subgroupOf_eq_of_le hQ, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [← coe_mul_of_left_le_normalizer_right _ _ (hD.trans hn), hj]

/-- Failing the third product bound fills the actual last-edge quotient.
The same statement applies to the smaller hat-fixed seed. -/
theorem endpoint_product_of_not_contained [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f u : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hfu : Adjacent R f u) (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (D : Subgroup (FreeAmalgam R)) (hHD : H R b ≤ D) (hD : D ≤ Q R u)
    (hnot : ¬ (D : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    (D : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R)) =
      (Q R u : Set (FreeAmalgam R)) := by
  have hu : color R u = true := by
    have hn := adjacent_color_ne R hfu
    cases h : color R u <;> simp_all
  have hHS := (Orbit.H_le_neighbor_U common earlier hb hmove).trans (U_le_Z R a)
  let := finite_stabilizer R u
  let : Finite D := Finite.of_injective
    (inclusion (hD.trans (show Q R u ≤ stabilizer R u from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hlarge : 2 < (Q R f).relIndex D := by
    by_contra! hh
    apply hnot
    exact (product_of_small_index hHD
      (preceding_H_not_le_endpoint common earlier ha hb hf hat hbt hmove hgen) hh).trans
        (Set.mul_subset_mul hHS (Set.Subset.refl _))
  exact product_eq_of_large_image hD (Q_le_adjacent_h R hu hfu)
    ((show Q R u ≤ stabilizer R f from fun _ hx => hx.2 f (adjacent_symm R hfu)).trans
      (Q_normalized R f)) (earlier.edge_Q_index f u hf hfu) hlarge

/-- The failed third bound gives the full preceding H as endpoint displacement. -/
theorem endpoint_commutator_eq_H [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t e f u : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (he : color R e = false) (hf : color R f = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (heu : Adjacent R e u) (hfu : Adjacent R f u)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hef : f ∈ Escape.movingNeighbors geometry e)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (D : Subgroup (FreeAmalgam R)) (hHD : H R b ≤ D) (hD : D ≤ Q R e)
    (hnot : ¬ (D : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    ⁅D, Z R f⁆ = H R e := by
  have hu : color R u = true := by
    have hn := adjacent_color_ne R hfu
    cases h : color R u <;> simp_all
  have hDQ := hD.trans (Q_le_adjacent_h R hu heu)
  have hp := endpoint_product_of_not_contained common earlier ha hb hf hat hbt hfu
    hmove hgen D hHD hDQ hnot
  have hn := (show Q R u ≤ stabilizer R f from
    fun _ hx => hx.2 f (adjacent_symm R hfu))
  have hj : Q R f ⊔ D = Q R u := by
    rw [sup_comm]
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right _ _ (hDQ.trans (hn.trans (Q_normalized R f)))]
    exact hp
  have hc := commutator_eq_of_centralizing_sup hj
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes f hf)))
    (hDQ.trans (hn.trans (Z_normalized R f)))
  rw [commutator_comm, hc]
  exact moving_edge_displacement_eq_H common earlier hf he hfu heu hef

/-- The first line of claim (3) on the original path, using its proved
relative generation and the actual preceding fixed seed. -/
theorem forward_failed_containment_commutator [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hD : normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 6)))
    (hnot : ¬ (normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))) :
    ⁅normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)), Z R (p.walk.getVert (i + 8))⁆ =
      H R (p.walk.getVert (i + 6)) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hie : Even (i + 6) := hi.add (by decide)
  have hif : Even (i + 8) := hi.add (by decide)
  apply endpoint_commutator_eq_H common earlier
    (t := p.walk.getVert (i - 1)) (u := p.walk.getVert (i + 7))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hie (by omega)) (p.even_color hif (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using
      p.adjacent (i := i - 2) (by omega)
  · simpa only [Nat.add_assoc] using p.adjacent (i := i + 6) (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 7) (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  · simpa only [Nat.add_assoc] using
      (p.moving_neighbors source common earlier hie (by omega) (by omega)).2
  · exact forward_generation common earlier p (firstFactsOnPath source common earlier p)
      hi (by omega) hi6
  · exact (H_le_fixedSeed common earlier (p.even_color hib (by omega))).trans
      (fixedSeed_le_span _ _ _)
  · exact hD
  · exact hnot


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third
