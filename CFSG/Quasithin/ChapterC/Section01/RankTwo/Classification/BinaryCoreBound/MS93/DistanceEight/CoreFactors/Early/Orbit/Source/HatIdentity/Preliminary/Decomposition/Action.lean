module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Local
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The literal first-hat quotient action

The carrier is hatV(b,a)/H_b inside the finite stabilizer G_b. Relative
normality and the moving-edge commutator bound descend conjugation through
the actual quotient G_b/Q_b onto SL₃(2). The action is faithful: triviality
would put the natural eight-group U_b inside H_b, whose order is at most four.
The displacement formula retains the actual ambient commutator and its H-index.
The forward and backward window constructors use the original supplied path.

This prepares the action used in the natural decomposition; no displacement
estimate or fixed-seed decomposition is assumed or asserted here.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
open PathCentrality
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

structure Window (geometry : Geometry R) (a b t : Vertex R) : Prop where
  color_a : color R a = false
  color_b : color R b = false
  adjacent_a : Adjacent R a t
  adjacent_b : Adjacent R b t
  moving : a ∈ Escape.movingNeighbors geometry b

noncomputable abbrev localHat (b a : Vertex R) := (hatV R b a).subgroupOf (stabilizer R b)
noncomputable abbrev localH (b : Vertex R) := (H R b).subgroupOf (stabilizer R b)

instance localHat_normal (b a : Vertex R) : (localHat b a).Normal :=
  normal_subgroupOf_of_le_normalizer (hatV_normalized R b a)

instance localH_normal (b : Vertex R) : (localH b).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R b, Q R b⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized b hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R b hg)]
  rfl

abbrev HatQuotient (b a : Vertex R) := localHat b a ⧸ (localH b).subgroupOf (localHat b a)

noncomputable def quotientProjection (b a : Vertex R) : localHat b a →* HatQuotient b a :=
  QuotientGroup.mk' _

noncomputable def localAction (b a : Vertex R) : stabilizer R b →* MulAut (HatQuotient b a) :=
  quotientAction (localHat b a) (localH b)

variable [Finite M]

instance quotient_finite (b a : Vertex R) : Finite (HatQuotient b a) := by
  let := finite_stabilizer R b
  infer_instance

omit [Finite M] in
theorem hat_le_local (earlier : Earlier R geometry) {a b t : Vertex R}
    (w : Window geometry a b t) : hatV R b a ≤ stabilizer R b :=
  (hatV_le_radius R (by rw [SimpleGraph.dist_comm, w.moving.1])).trans
    ((V_le_Q R w.color_b (by rw [earlier.distance]; decide)).trans (fun _ hx => hx.1))

theorem H_le_hat (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t) : H R b ≤ hatV R b a :=
  (H_le_Z_of_central common w.color_b (earlier.centrality b w.color_b)).trans
    (Z_le_hatV w.color_b w.moving.1)

omit [Finite M] in
theorem quotient_elementary (earlier : Earlier R geometry) {a b t : Vertex R}
    (w : Window geometry a b t) : IsElementaryAbelian 2 (HatQuotient b a) := by
  let : IsElementaryAbelian 2 (hatV R b a) :=
    localZSpan_elementary R w.color_b
      (by rw [SimpleGraph.dist_comm, w.moving.1]) (by rw [earlier.distance]; decide)
  let : IsElementaryAbelian 2 (localHat b a) :=
    IsElementaryAbelian.subgroupOf (hat_le_local earlier w)
  exact IsElementaryAbelian.of_surjective (quotientProjection b a)
    (QuotientGroup.mk'_surjective _)

theorem localAction_kills_Q (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t) :
    (Q R b).subgroupOf (stabilizer R b) ≤ (localAction b a).ker := by
  apply quotientAction_kills (localHat b a) (localH b)
  have h := hatV_commutator_le_H common earlier w.color_a w.color_b
    w.adjacent_a w.adjacent_b w.moving
  apply (map_le_iff_le_comap).mp
  rw [map_commutator, map_subgroupOf_eq_of_le (hat_le_local earlier w),
    map_subgroupOf_eq_of_le (show Q R b ≤ stabilizer R b from fun _ hx => hx.1)]
  exact h

noncomputable def headAction (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t) :
    SL →* MulAut (HatQuotient b a) :=
  (localProjection source b w.color_b).liftOfSurjective
    (localProjection_surjective source b w.color_b) ⟨localAction b a, by
      rw [localProjection_kernel]
      exact localAction_kills_Q common earlier w⟩

theorem headAction_comp (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t) :
    (headAction common earlier w).comp (localProjection source b w.color_b) =
      localAction b a := by
  ext g v
  unfold headAction
  rw [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]

theorem headAction_apply (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t)
    (g : stabilizer R b) (v : localHat b a) :
    headAction common earlier w (localProjection source b w.color_b g)
      (quotientProjection b a v) = quotientProjection b a
        ⟨g * (v : stabilizer R b) * g⁻¹,
          (inferInstance : (localHat b a).Normal).conj_mem v v.property g⟩ := by
  have he := congrArg (fun f : stabilizer R b →* MulAut (HatQuotient b a) =>
    f g (quotientProjection b a v)) (headAction_comp common earlier w)
  exact he.trans (quotientAction_apply (localHat b a) (localH b) g v)


theorem displacement_card (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t)
    (J : Subgroup (FreeAmalgam R)) (hJ : J ≤ stabilizer R b) :
    Nat.card (commutatorAction
      (((J.subgroupOf (stabilizer R b)).map (localProjection source b w.color_b)).map
        (headAction common earlier w)) (HatQuotient b a)) =
      (H R b).relIndex ⁅hatV R b a, J⁆ := by
  let := finite_stabilizer R b
  rw [map_map, headAction_comp]
  change Nat.card (commutatorAction
    ((J.subgroupOf (stabilizer R b)).map (quotientAction (localHat b a) (localH b)))
      (HatQuotient b a)) = _
  rw [quotientAction_displacement_card]
  have h := relIndex_map_map_of_injective (localH b)
    ⁅localHat b a, J.subgroupOf (stabilizer R b)⁆ (stabilizer R b).subtype_injective
  rw [map_subgroupOf_eq_of_le
      ((H_le_Z_of_central common w.color_b (earlier.centrality b w.color_b)).trans
        (Z_le_stabilizer R b)), map_commutator,
    map_subgroupOf_eq_of_le (hat_le_local earlier w), map_subgroupOf_eq_of_le hJ] at h
  exact h.symm

theorem headAction_injective (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t) :
    Function.Injective (headAction common earlier w) := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply (headAction common earlier w).ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker (headAction common earlier w)).eq_bot_or_eq_top with hk | hk
  · exact hk
  have hc : ⁅localHat b a, (⊤ : Subgroup (stabilizer R b))⁆ ≤ localH b := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro g _ v hv
    have hg : headAction common earlier w (localProjection source b w.color_b g) = 1 :=
      MonoidHom.mem_ker.mp (hk ▸ mem_top _)
    have he := headAction_apply common earlier w g ⟨v, hv⟩
    rw [hg] at he
    have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
    change g * v * g⁻¹ / v ∈ localH b at hh
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  have hamb : ⁅hatV R b a, stabilizer R b⁆ ≤ H R b := by
    have hh := map_mono (f := (stabilizer R b).subtype) hc
    rw [map_commutator, map_subgroupOf_eq_of_le (hat_le_local earlier w),
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.trans (map_le_iff_le_comap.mpr le_rfl)
  have hU : U R b ≤ H R b :=
    (commutator_mono (Z_le_hatV w.color_b w.moving.1) (Ltilde_le_stabilizer b)).trans hamb
  let := finite_stabilizer R b
  have hHS : H R b ≤ stabilizer R b := (H_le_hat common earlier w).trans (hat_le_local earlier w)
  let : Finite (H R b) := Finite.of_injective (inclusion hHS) (inclusion_injective hHS)
  have hcard := card_le_of_le hU
  rw [common.natural.card_at b w.color_b] at hcard
  have hsmall := H_card_le_four common earlier w.color_b
  omega

theorem forwardWindow (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    Window geometry (p.walk.getVert i) (p.walk.getVert (i - 2)) (p.walk.getVert (i - 1)) := by
  have hb : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  refine ⟨p.even_color hi (by omega), p.even_color hb (by omega), ?_, ?_, ?_⟩
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using
      p.adjacent (i := i - 2) (by omega)
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hb (by omega) (by omega)).2

theorem backwardWindow (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    Window geometry (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 1)) := by
  have hb : Even (i + 2) := hi.add (by decide)
  refine ⟨p.even_color hi (by omega), p.even_color hb (by omega), p.adjacent (by omega), ?_, ?_⟩
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hb (by omega) (by omega)).1


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
