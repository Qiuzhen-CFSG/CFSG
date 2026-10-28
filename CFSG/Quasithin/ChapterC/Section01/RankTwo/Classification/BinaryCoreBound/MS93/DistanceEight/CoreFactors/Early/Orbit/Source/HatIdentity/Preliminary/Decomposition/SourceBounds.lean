module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.Bounds
public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupAction.FourthPowerFixed

/-!
# Source bounds for the actual first-hat action

The first kernel calculation has index at most two in the radius group.
On that intersection, the endpoint displacement is contained in the critical
Z-commutator, whose order is two. Restricting a homomorphism to an index-two
subgroup therefore bounds the full displacement image by four. This is applied
to an actual nontrivial endpoint involution on hatV/H, preserving the literal
local projection and quotient map.

The checked three-conjugate theorem now bounds both the moving dimension and
fixed-space codimension by six, in all four configurations on the original
source path. No displacement or dimension premise remains. The subsequent
fixed-seed decomposition is a separate step and is not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), opening calculation,
printed p.897; the three-conjugate argument is (1.1)(i), pp.832--833.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition

private theorem card_range_le_index_mul_card_map {A E : Type*} [Group A] [Group E]
    [Finite A] (f : A →* E) (K : Subgroup A) :
    Nat.card f.range ≤ K.index * Nat.card (K.map f) := by
  let N := K.map f
  have hle : N ≤ f.range := map_le_range f K
  have hc := relIndex_mul_relIndex (⊥ : Subgroup E) N f.range bot_le hle
  rw [relIndex_bot_left, relIndex_bot_left] at hc
  have hi : N.relIndex f.range ≤ K.index := by
    rw [← index_comap]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (K.index_ne_zero_of_finite))
      (index_dvd_of_le (le_comap_map f K))
  rw [← hc, mul_comm]
  exact Nat.mul_le_mul_right _ hi

private def differenceHom {E : Type*} [Group E] [IsMulCommutative E]
    (a : MulAut E) : E →* E where
  toFun w := a w / w
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, div_eq_mul_inv, mul_inv_rev]; ac_rfl

private theorem difference_range_card {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (a : MulAut E) (ha : a ^ 2 = 1) :
    Nat.card (differenceHom a).range = Nat.card (commutatorAction (zpowers a) E) := by
  have hk : (differenceHom a).ker = FixedPoints.subgroup (zpowers a) E := by
    ext x
    rw [MonoidHom.mem_ker, MulAut.mem_fixed_zpowers_iff]
    change a x / x = 1 ↔ a x = x
    exact div_eq_one
  have hc := (differenceHom a).ker.card_mul_index
  rw [index_ker, hk] at hc
  have hD := (MulAut.involution_fixed_displacement_card_data a ha).1
  have hpos : 0 < Nat.card (FixedPoints.subgroup (zpowers a) E) := Nat.card_pos
  nlinarith

private theorem small_displacement_of_index_two {A E : Type*} [Group A] [Group E]
    [Finite A] [Finite E] [IsElementaryAbelian 2 E]
    (q : A →* E) (hq : Function.Surjective q) (a : MulAut E) (ha : a ^ 2 = 1)
    (K : Subgroup A) (hindex : K.index ≤ 2) (N : Subgroup E) (hcard : Nat.card N ≤ 2)
    (hsmall : ∀ x ∈ K, a (q x) / q x ∈ N) :
    Nat.card (commutatorAction (zpowers a) E) ≤ 4 := by
  let f := (differenceHom a).comp q
  have hle : K.map f ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsmall x hx
  have hc : Nat.card (K.map f) ≤ 2 := (card_le_of_le hle).trans hcard
  have hr : f.range = (differenceHom a).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hq, ← MonoidHom.range_eq_map]
  have hb := card_range_le_index_mul_card_map f K
  rw [hr, difference_range_card a ha] at hb
  have hp := Nat.mul_le_mul hindex hc
  exact hb.trans hp

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
open Escape.Initial.Natural.Splitting

private theorem critical_commutator_card (common : CommonFacts R source geometry)
    {b f : Vertex R} (hb : color R b = false)
    (hc : CriticalPair R b f (geometry.exists_critical b hb)) :
    Nat.card (⁅Z R b, Z R f⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  let n := LocalCommutator.naturalStructure common
  have hf := critical_endpoint_color R b hb _ hc
  rw [n.critical_commutator_eq geometry b hb f hc]
  let : Finite (U R b) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at b hb]; decide)
  let : Finite (U R f) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at f hf]; decide)
  let := geometry.U_elementary (by have := common.large_distance; omega) b hb
  let := geometry.U_elementary (by have := common.large_distance; omega) f hf
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry b hb f hc
  exact card_commutator_eq_two_of_elementary_eight _ _
    (common.natural.card_at b hb) (common.natural.card_at f hf) hn hn'
    (n.critical_U_noncommutation geometry b hb f hc)


/-- The first two source calculations bound a nontrivial endpoint involution
on the literal first-hat quotient. The actual quotient and critical endpoint
are retained; the actor is not replaced by a module-type label. -/
theorem actionBounds_of_critical_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t e f : Vertex R} (w : Window geometry a b t)
    (hc : CriticalPair R b f (geometry.exists_critical b w.color_b))
    (hindex : (Q R e).relIndex (V R b) ≤ 2)
    (hprod : (V R b ⊓ Q R e : Set (FreeAmalgam R)) ⊆
      (Z R b : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    ActionBounds common earlier w := by
  have hf := critical_endpoint_color R b w.color_b _ hc
  have hr := common.critical_reverse b w.color_b f hf hc
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hr.2
  have hZlocal : Z R f ≤ stabilizer R b := by
    apply geometry.Z_le_stabilizer_of_dist_le_b f hf
    rw [SimpleGraph.dist_comm, hc.1, geometry.distance_constant b w.color_b]
    exact le_rfl
  let z₀ : stabilizer R b := ⟨z, hZlocal hz⟩
  let u := localProjection source b w.color_b z₀
  have hu : u ≠ 1 := by
    intro hu
    have hh : z₀ ∈ (localProjection source b w.color_b).ker := hu
    rw [localProjection_kernel] at hh
    exact hzQ hh
  have hu2 : u ^ 2 = 1 := by
    let := geometry.Z_elementary (by have := common.large_distance; omega) f hf
    rw [← map_pow, show z₀ ^ 2 = 1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz), map_one]
  apply actionBounds_of_small_displacement common earlier w u hu hu2
  let := quotient_elementary earlier w
  let := finite_stabilizer R b
  let j : localHat b a →* FreeAmalgam R :=
    (stabilizer R b).subtype.comp (localHat b a).subtype
  have hj : Function.Injective j :=
    (stabilizer R b).subtype_injective.comp (localHat b a).subtype_injective
  have hjrange : j.range = hatV R b a := by
    rw [MonoidHom.range_comp, range_subtype, map_subgroupOf_eq_of_le (hat_le_local earlier w)]
  let K := (Q R e).comap j
  have hK : K.index ≤ 2 := by
    rw [show K.index = (Q R e).relIndex j.range from index_comap _ _, hjrange]
    have hhat : hatV R b a ≤ V R b :=
      hatV_le_radius R (by rw [SimpleGraph.dist_comm, w.moving.1])
    exact (relIndex_le_of_le_right hhat (by
      let : Finite (V R b) := Finite.of_injective
        (inclusion (geometry.V_local b w.color_b (by
          rw [geometry.distance_constant b w.color_b]; exact common.large_distance))) (inclusion_injective _)
      exact index_ne_zero_of_finite)).trans hindex
  let N := ⁅Z R b, Z R f⁆
  have hN : Nat.card N = 2 := critical_commutator_card common w.color_b hc
  let : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; decide)
  let N₀ := N.comap j
  let Nq := N₀.map (quotientProjection b a)
  have hNq : Nat.card Nq ≤ 2 := by
    have hmap : Nat.card Nq ≤ Nat.card N₀ := Nat.card_le_card_of_surjective
      (fun x : N₀ => (⟨quotientProjection b a x.val, mem_map_of_mem _ x.property⟩ : Nq))
      (by rintro ⟨y, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
    apply hmap.trans
    have hn : Nat.card N₀ ≤ Nat.card N := Nat.card_le_card_of_injective
      (fun x : N₀ => (⟨j x.val, x.property⟩ : N)) (fun x y h =>
        Subtype.ext (hj (congrArg (fun v : N => (v : FreeAmalgam R)) h)))
    exact hn.trans hN.le
  apply small_displacement_of_index_two (quotientProjection b a)
    (QuotientGroup.mk'_surjective _) (headAction common earlier w u)
    (by rw [← map_pow, hu2, map_one]) K hK Nq hNq
  intro x hx
  change headAction common earlier w (localProjection source b w.color_b z₀)
    (quotientProjection b a x) / quotientProjection b a x ∈ Nq
  rw [headAction_apply, ← map_div]
  apply mem_map_of_mem (quotientProjection b a)
  change z * j x * z⁻¹ / j x ∈ N
  have hxV : j x ∈ V R b :=
    (hatV_le_radius R (by rw [SimpleGraph.dist_comm, w.moving.1])) x.property
  obtain ⟨d, hd, q, hq, he⟩ := hprod ⟨hxV, hx⟩
  have hqcomm : ⁅z, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes f hf)) hq z hz)
  have hdN : ⁅z, d⁆ ∈ N := by
    change ⁅z, d⁆ ∈ ⁅Z R b, Z R f⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hz hd
  have hcomm : ⁅z, j x⁆ ∈ N := by
    rw [← he, commutatorElement_mul_right_eq_mul_conj, hqcomm, mul_one, mul_inv_cancel_right]
    exact hdN
  simpa only [commutatorElement_def, div_eq_mul_inv] using hcomm


private theorem forward_kernel_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi6 : i ≤ 6) :
    (Q R (p.walk.getVert (i + 6))).relIndex (V R (p.walk.getVert i)) ≤ 2 := by
  have ha := p.even_color hi (by omega)
  have he := p.even_color (hi.add (by decide : Even 6)) (by omega)
  exact First.Kernel.Detection.radius_kernel_index_le_two common earlier ha he
    (show Adjacent R (p.walk.getVert (i + 6)) (p.walk.getVert (i + 5)) from
      adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega)))
    (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i + 5)) = 5 by
      rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (show (cosetGraph R).dist (p.walk.getVert (i + 6)) (p.walk.getVert (i + 4)) ≤ 2 by
      rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (p.first_commutator source common earlier hi hi2 (by omega)).2

private theorem backward_kernel_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    (Q R (p.walk.getVert (i - 6))).relIndex (V R (p.walk.getVert i)) ≤ 2 := by
  have hi6 : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have ha := p.even_color hi (by omega)
  have he := p.even_color hi6 (by omega)
  exact First.Kernel.Detection.radius_kernel_index_le_two common earlier ha he
    (show Adjacent R (p.walk.getVert (i - 6)) (p.walk.getVert (i - 5)) from
      by simpa only [show i - 6 + 1 = i - 5 by omega] using
        p.adjacent (i := i - 6) (by omega))
    (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i - 5)) = 5 by
      rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (show (cosetGraph R).dist (p.walk.getVert (i - 6)) (p.walk.getVert (i - 4)) ≤ 2 by
      rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (p.first_commutator_backward source common earlier hi hi8 hi12).2

/-- All four actual quotient actions satisfy the three-conjugate dimension
bounds, using the first source calculations and no action-bound premise. -/
theorem actionBoundsOnPath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) :
    ActionBoundsOnPath common earlier p := by
  constructor
  · intro i hi hi4 hi6 _
    have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
    apply actionBounds_of_critical_kernel common earlier (forwardWindow common earlier p hi hi4 hi6)
      (p.critical_pair earlier hib (by omega))
      (forward_kernel_index common earlier p hib (by omega) (by omega))
    exact ((firstFactsOnPath source common earlier p).forward (i - 2) hib (by omega) (by omega)).intersection_product_le
  · intro i hi hi8 hi10 _
    have hib : Even (i + 2) := hi.add (by decide)
    have hif : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
    have hc := p.critical_pair earlier hif (by omega)
    rw [show i - 6 + 8 = i + 2 by omega] at hc
    have hr := common.critical_reverse _ (p.even_color hif (by omega)) _
      (p.even_color hib (by omega)) hc
    apply actionBounds_of_critical_kernel common earlier (backwardWindow common earlier p hi hi8 hi10) hr
    · simpa only [show i + 2 - 6 = i - 4 by omega] using
        backward_kernel_index common earlier p hib (by omega) (by omega)
    · simpa only [show i + 2 - 6 = i - 4 by omega,
        show i + 2 - 8 = i - 6 by omega] using
        ((firstFactsOnPath source common earlier p).backward (i + 2) hib (by omega) (by omega)).intersection_product_le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
