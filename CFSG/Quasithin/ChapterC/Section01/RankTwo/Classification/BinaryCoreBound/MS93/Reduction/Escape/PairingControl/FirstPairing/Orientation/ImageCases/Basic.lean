module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths

/-!
# Common geometry and order comparisons for the first image split

The image is the actual image of V at the second predecessor in the starting
vertex quotient by Q. Critical noncommutation excludes image order one.
The bound b ≥ 6 makes each radius-two group abelian, and in particular R₀
centralizes the intersection used in the order-two case. A quotient-image
lower bound of four, when established, identifies the intersection commutator
with the whole moving-neighbor commutator of order at most four.

The front path retains three vertices of the original geodesic. These results
do not supply either of the representation estimates in the two image cases.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The actual vertices alpha+1, alpha+2 and alpha+3 on the chosen path. -/
structure FrontPath (p : Counterexample geometry) where
  first : Vertex R
  second : Vertex R
  third : Vertex R
  first_before : Before p.a' p.a first 1
  second_before : Before p.a' p.a second 2
  third_before : Before p.a' p.a third 3

/-- Choose all three vertices on the original critical geodesic. -/
noncomputable def frontPath (p : Counterexample geometry) (h : 6 ≤ geometry.b R) :
    FrontPath p := by
  have he (n : ℕ) (hn : n ≤ geometry.b R) : ∃ d, Before p.a' p.a d n := by
    obtain ⟨d, hd⟩ := p.exists_before (Nat.sub_le (geometry.b R) n)
    refine ⟨d, ?_⟩
    have hh := Geometry.before_reverse hd
    simpa only [p.distance_eq_b, Nat.sub_sub_self hn] using hh
  exact ⟨(he 1 (by omega)).choose, (he 2 (by omega)).choose,
    (he 3 (by omega)).choose, (he 1 (by omega)).choose_spec,
    (he 2 (by omega)).choose_spec, (he 3 (by omega)).choose_spec⟩

namespace FrontPath
variable {p : Counterexample geometry} (path : FrontPath p)

theorem start_first_adjacent : Adjacent R p.a path.first :=
  path.first_before.endpoint_adjacent

theorem second_first_adjacent : Adjacent R path.second path.first :=
  path.second_before.adjacent (geometry := geometry) path.first_before

theorem third_second_adjacent : Adjacent R path.third path.second :=
  path.third_before.adjacent (geometry := geometry) path.second_before

theorem second_color : color R path.second = false :=
  (path.second_before.color (by decide)).trans p.color_a

theorem first_color : color R path.first = true := by
  have h := adjacent_color_ne R path.start_first_adjacent
  cases hc : color R path.first <;> simp_all [p.color_a]

theorem third_color : color R path.third = true := by
  have h := adjacent_color_ne R path.third_second_adjacent
  cases hc : color R path.third <;> simp_all [path.second_color]

theorem start_second_distance : (cosetGraph R).dist p.a path.second = 2 := by
  rw [SimpleGraph.dist_comm]
  exact path.second_before.1

variable [Finite M]

theorem second_kernel_le_first : Q R path.second ≤ Q R path.first :=
  Q_le_adjacent_h R path.first_color path.second_first_adjacent

theorem start_commutator_le_edge :
    ⁅Z R p.a, Q R path.second⁆ ≤ edgeDisplacement p.a path.first :=
  commutator_mono le_rfl path.second_kernel_le_first

end FrontPath

variable [Finite M]

theorem predecessor_V_le_start_stabilizer (p : Counterexample geometry) :
    V R p.c ≤ stabilizer R p.a := by
  apply Geometry.V_le_stabilizer_of_distance p.before_color
  have h := p.before.2
  rw [p.distance_eq_b] at h
  rw [SimpleGraph.dist_comm]
  omega

/-- Positive positions before the start-side end of the critical path place
V_c in the actual neighborhood kernel, by critical minimality. -/
theorem predecessor_V_le_path_kernel (p : Counterexample geometry)
    {d : Vertex R} {n : ℕ} (hd : Before p.a' p.a d n)
    (hn : 0 < n) (hnb : n + 2 ≤ geometry.b R) : V R p.c ≤ Q R d := by
  have hrev := Geometry.before_reverse p.before
  have hdist := Geometry.before_distance (geometry := geometry) hrev hd
    (show n ≤ (cosetGraph R).dist p.a p.a' - 2 by rw [p.distance_eq_b]; omega)
  rw [p.distance_eq_b] at hdist
  apply Geometry.V_le_Q_of_distance p.before_color
  omega

/-- This is normality in V at the predecessor, not normality in the amalgam. -/
theorem intersection_normal (p : Counterexample geometry) :
    ((V R p.c ⊓ Q R p.a).subgroupOf (V R p.c)).Normal := by
  rw [inf_subgroupOf_left]
  exact normal_subgroupOf_of_le_normalizer
    ((predecessor_V_le_start_stabilizer p).trans (Q_normalized R p.a))

omit [Finite M] in
theorem end_Z_le_predecessor_V (p : Counterexample geometry) :
    Z R p.a' ≤ V R p.c := by
  apply le_iSup_of_le p.a'
  apply le_iSup_of_le
    (show (cosetGraph R).dist p.a' p.c ≤ 2 by
      rw [SimpleGraph.dist_comm, p.before.1])
  exact le_rfl

theorem predecessor_V_not_le_start_kernel (source : LocalSource L R)
    (p : Counterexample geometry) : ¬ V R p.c ≤ Q R p.a := by
  intro h
  exact (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    ((end_Z_le_predecessor_V p).trans h)

theorem image_order_ge_two (source : LocalSource L R) (hb : 2 < geometry.b R)
    (p : Counterexample geometry) : 2 ≤ (Q R p.a).relIndex (V R p.c) := by
  let := finite_stabilizer R p.c
  let : Finite (V R p.c) := Finite.of_injective
    (inclusion ((geometry.V_le_Q hb p.c p.before_color).trans
      (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hzero := ((Q R p.a).subgroupOf (V R p.c)).index_ne_zero_of_finite
  have hone : (Q R p.a).relIndex (V R p.c) ≠ 1 :=
    fun h => predecessor_V_not_le_start_kernel source p (relIndex_eq_one.mp h)
  change (Q R p.a).relIndex (V R p.c) ≠ 0 at hzero
  omega

theorem image_order_eq_two (source : LocalSource L R) (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (h : ¬ 2 < (Q R p.a).relIndex (V R p.c)) :
    (Q R p.a).relIndex (V R p.c) = 2 := by
  have := image_order_ge_two source hb p
  omega

/-- The radius commutator and the intersection both lie in the abelian V_c. -/
theorem radius_centralizes_intersection (p : Counterexample geometry)
    (ip : InitialFacts p) :
    radiusCommutator p.a p.a' ≤
      centralizer (V R p.c ⊓ Q R p.a : Set (FreeAmalgam R)) := by
  have h := Geometry.V_centralizes_V_of_distance p.before_color p.before_color
    (show (cosetGraph R).dist p.c p.c + 4 < geometry.b R by
      simpa only [SimpleGraph.dist_self, zero_add] using (by have := ip.six_le; omega :
        4 < geometry.b R))
  exact (p.radius_le_end.trans (end_Z_le_predecessor_V p)).trans
    (h.trans (centralizer_le inf_le_left))

/-- The index-two intersection loses at most a factor two in the fixed quotient.
The natural-section lower bound of eight remains an explicit premise here. -/
theorem intersection_index_ge_four (hb : 2 < geometry.b R)
    (p : Counterexample geometry)
    (hi : (Q R p.a).relIndex (V R p.c) = 2)
    (hnatural : 8 ≤ (B R p.c (geometry.Z_normal p.c)).relIndex (V R p.c)) :
    4 ≤ (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).relIndex
      (V R p.c ⊓ Q R p.a) := by
  let := finite_stabilizer R p.c
  let : Finite (V R p.c) := Finite.of_injective
    (inclusion ((geometry.V_le_Q hb p.c p.before_color).trans
      (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hmul := relIndex_inf_mul_relIndex (B R p.c (geometry.Z_normal p.c))
    (Q R p.a) (V R p.c)
  rw [hi, inf_comm (Q R p.a)] at hmul
  have hmono := relIndex_le_of_le_left
    (show B R p.c (geometry.Z_normal p.c) ⊓ Q R p.a ≤
      B R p.c (geometry.Z_normal p.c) from inf_le_left)
    (L := V R p.c) (index_ne_zero_of_finite)
  have heq : (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).relIndex
      (V R p.c ⊓ Q R p.a) =
      (B R p.c (geometry.Z_normal p.c)).relIndex (V R p.c ⊓ Q R p.a) := by
    rw [← inf_relIndex_right (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)),
      ← inf_relIndex_right (B R p.c (geometry.Z_normal p.c))]
    congr 1
    ext x
    simp only [mem_inf]
    tauto
  rw [heq]
  omega

/-- A lower bound for the actual image modulo D_c fills the whole commutator,
whose order is at most four. No commutator order is postulated in this lemma. -/
theorem moving_commutator_eq_of_image_lower (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) {d : Vertex R}
    (hd : d ∈ movingNeighbors geometry p.a)
    (hlarge : 4 ≤ (fixedCore R p.c).relIndex
      (⁅Z R d, V R p.c ⊓ Q R p.a⁆ : Subgroup (FreeAmalgam R))) :
    ⁅Z R d, V R p.c ⊓ Q R p.a⁆ = ⁅Z R d, Q R p.a⁆ := by
  have hle : ⁅Z R d, V R p.c ⊓ Q R p.a⁆ ≤ ⁅Z R d, Q R p.a⁆ :=
    commutator_mono le_rfl inf_le_right
  have hlocal : ⁅Z R d, Q R p.a⁆ ≤ stabilizer R d :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Q_le_stabilizer_of_dist_two R p.a d p.color_a hd.1).trans
        (Z_normalized R d))).trans (Z_le_stabilizer R d)
  let := finite_stabilizer R d
  let : Finite (⁅Z R d, Q R p.a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hlocal) (inclusion_injective _)
  let : Finite (⁅Z R d, V R p.c ⊓ Q R p.a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hcard : 4 ≤ Nat.card (⁅Z R d, V R p.c ⊓ Q R p.a⁆ : Subgroup (FreeAmalgam R)) :=
    hlarge.trans (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _))
  exact eq_of_le_of_card_ge hle
    ((moving_commutator_card_le_four source hb modules p.color_a hd).trans hcard)

private theorem fixed_preimage_normalized (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ≤ normalizer (B R a (geometry.Z_normal a) : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (B R a (geometry.Z_normal a)).map (MulAut.conj g).toMonoidHom = _
  have h := B_act hb g⁻¹ a ha
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

/-- The denominator in the small intersection quotient is normal in that
intersection, with normalization proved inside the vertex stabilizer. -/
theorem intersection_fixed_denominator_normal (hb : 2 < geometry.b R)
    (p : Counterexample geometry) :
    ((V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).subgroupOf
      (V R p.c ⊓ Q R p.a)).Normal := by
  have heq : (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).subgroupOf
      (V R p.c ⊓ Q R p.a) =
      (B R p.c (geometry.Z_normal p.c)).subgroupOf (V R p.c ⊓ Q R p.a) := by
    ext x
    change (x.val ∈ V R p.c ∧ x.val ∈ B R p.c (geometry.Z_normal p.c)) ↔ _
    exact ⟨And.right, fun hx => ⟨x.property.1, hx⟩⟩
  rw [heq]
  apply normal_subgroupOf_of_le_normalizer
  exact (inf_le_left.trans ((geometry.V_le_Q hb p.c p.before_color).trans
    (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1))).trans
      (fixed_preimage_normalized hb p.c p.before_color)

/-- The intersection commutator lies in Q_c, so its image modulo D_c is
formed entirely in a finite local group. -/
theorem intersection_commutator_le_predecessor_kernel (hb : 2 < geometry.b R)
    (p : Counterexample geometry) {d : Vertex R}
    (hd : d ∈ movingNeighbors geometry p.a) :
    ⁅Z R d, V R p.c ⊓ Q R p.a⁆ ≤ Q R p.c :=
  (Subgroup.commutator_le_sup _ _).trans (sup_le ((moving_Z_le_V hd).trans p.trapped)
    (inf_le_left.trans (geometry.V_le_Q hb p.c p.before_color)))

/-- The commutator-image denominator is normal in the actual commutator. -/
theorem commutator_image_denominator_normal (hb : 2 < geometry.b R)
    (p : Counterexample geometry) {d : Vertex R}
    (hd : d ∈ movingNeighbors geometry p.a) :
    ((fixedCore R p.c).subgroupOf
      (⁅Z R d, V R p.c ⊓ Q R p.a⁆ : Subgroup (FreeAmalgam R))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact ((intersection_commutator_le_predecessor_kernel hb p hd).trans
    (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1)).trans
      (fixedCore_normalized p.c)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
