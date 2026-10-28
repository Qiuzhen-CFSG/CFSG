module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.LargeImage.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Generic

/-!
# Capturing the all-rho displacement in MS93 (4.4.1)

Write d for the backward vertex, e for the endpoint and t = e-4. The
all-rho fixedness assumption makes [V_x,Q_x,Ltilde_x] lie in Z_x at every
M-vertex. Relative normalization and neighbor generation then put [V_x,Q_x]
in every incident odd-vertex radius group. The literal odd radius has only
its neighboring M-type Z-generators; critical minimality makes the first
such radius centralize V_t and the radius at e-3 centralize Z_e.

The backward displacement E = [Z_d,Q_c] has order four in the actual natural
subgroup U_d of order eight. It centralizes V_t. Evaluation at an element
of U_d outside E detects the full action of V_t on U_d, since E has index
two and is fixed. The marked natural action has exact kernel Q_d, so the
assumed image bound greater than two forces E into [U_d,V_t], hence into
[Z_d,V_t]. The latter lies in [V_t,Q_t], giving its endpoint centrality.

Only the second image bound is needed after it is supplied. In particular,
these conditional conclusions add no natural-section or neighboring-radius
premise. The parent supplies the image bound and performs the contradiction
with the backward witness's nontrivial triple commutator.

The neighboring-displacement argument adapts `neighbor_radical_bound` in
Reduction/Escape/PairingControl/FirstPairing/Orientation/ImageCases/LargeImage/
Geometry.lean, retaining just the triple bound used by that proof. It does
not use that module's contrary escape hypotheses or its natural section.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), printed p.892, the all-rho paragraph after claim (3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
open Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}
/-- Residual-fixed kernel displacement lies in every incident odd radius.
Normality is relative to the vertex stabilizer throughout. -/
theorem radius_displacement_le_neighbor_of_triple (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (htriple : ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a) :
    ⁅V R a, Q R a⁆ ≤ V R t := by
  let W := V R t
  let N := Z R a ⊔ ⁅W, Q R a⁆
  have hQG : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hVG : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans hQG
  have hWV : W ≤ V R a := adjacent_V_le ha hat
  have hZW : Z R a ≤ W := by
    apply le_iSup_of_le a
    apply le_iSup_of_le (show (cosetGraph R).dist a t ≤ 2 by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
      decide)
    exact le_rfl
  have hQW : Q R a ≤ normalizer (W : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans (V_normalized R t)
  have hNW : N ≤ W := sup_le hZW (le_normalizer_iff_commutator_le_left.mp hQW)
  have hQN : Q R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (le_inf (hQG.trans (Z_normalized R a)) (normalizer_commutator_ge_right W (Q R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNL : ⁅N, Ltilde R a⁆ ≤ Z R a := by
    let P := commutatorPreimage (stabilizer R a) (Ltilde R a) (Z R a)
    have hZP : Z R a ≤ P := le_commutatorPreimage (Z_le_stabilizer R a)
      (le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a).trans (Z_normalized R a)))
    have hWP : ⁅W, Q R a⁆ ≤ P := by
      apply le_commutatorPreimage
        ((le_normalizer_iff_commutator_le_left.mp hQW).trans (hWV.trans hVG))
      exact (commutator_mono (commutator_mono hWV le_rfl) le_rfl).trans
        htriple
    exact (commutator_mono (sup_le hZP hWP) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R a))
  have hLN : Ltilde R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hNL.trans le_sup_left)
  have hGN : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    exact sup_le hLN hQN
  let C := commutatorPreimage (V R a) (Q R a) N
  have hGC : stabilizer R a ≤ normalizer (C : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ (hVG.trans hGN)
      (V_normalized R a) (Q_normalized R a) hGN
  have hWC : W ≤ C := le_commutatorPreimage hWV le_sup_right
  exact ((commutator_mono (V_le_of_normalized_neighbor ha hat C hGC hWC) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (hVG.trans hGN))).trans hNW


/-- A fixed subgroup of index two detects the whole action on its overgroup
by evaluation at one element outside it. -/
private theorem capture_index_two {G : Type*} [Group G]
    (U E K : Subgroup G) [Finite U] [Finite K]
    (hEU : E ≤ U) (hE : Nat.card E = 4) (hU : Nat.card U = 8)
    (hEK : E ≤ centralizer (K : Set G))
    (hUK : ⁅U, K⁆ ≤ E)
    (hlarge : 2 < (centralizer (U : Set G)).relIndex K) : E ≤ ⁅U, K⁆ := by
  classical
  let H := ⁅U, K⁆
  have hHU : H ≤ U := hUK.trans hEU
  let : Finite E := Finite.of_injective (inclusion hEU) (inclusion_injective hEU)
  let : Finite H := Finite.of_injective (inclusion hHU) (inclusion_injective hHU)
  have hidx : E.relIndex U = 2 := by
    have hh := (E.subgroupOf U).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv, hE, hU] at hh
    change E.relIndex U * 4 = 8 at hh
    omega
  obtain ⟨z, hzU, hzE⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ U ≤ E from fun h => by
      have hh := congrArg (fun A : Subgroup G => Nat.card A) (le_antisymm h hEU)
      rw [hU, hE] at hh
      omega)
  have hgen : U ≤ zpowers z ⊔ centralizer (K : Set G) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact mem_sup_right (hEK hxE)
    · have hk : z⁻¹ * x ∈ E := by
        have hh := (E.subgroupOf U).mul_mem_iff_of_index_two hidx
          (a := ⟨z⁻¹, U.inv_mem hzU⟩) (b := ⟨x, hx⟩)
        exact hh.mpr (by simp only [mem_subgroupOf, inv_mem_iff, hzE, hxE])
      have hh := (zpowers z ⊔ centralizer (K : Set G)).mul_mem
        (mem_sup_left (mem_zpowers z)) (mem_sup_right (hEK hk))
      simpa only [mul_inv_cancel_left] using hh
  have hKU : ⁅K,U⁆ ≤ H := by rw [commutator_comm]
  have hHK : H ≤ centralizer (K : Set G) := hUK.trans hEK
  let f := RankOnePairing.evaluation K U H hKU hHK ⟨z,hzU⟩
  have hk : f.ker = (centralizer (U : Set G)).subgroupOf K :=
    RankOnePairing.evaluation_ker_of_cyclic K U H hKU hHK ⟨z,hzU⟩ hgen
  have hsize : 2 < Nat.card H := by
    have hf := Subgroup.index_ker f
    rw [hk] at hf
    change (centralizer (U : Set G)).relIndex K = Nat.card f.range at hf
    exact (hlarge.trans_eq hf).trans_le
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
  have hdvd : Nat.card H ∣ 4 := hE ▸ card_dvd_of_le hUK
  have hle : Nat.card H ≤ 4 := hE ▸ card_le_of_le hUK
  have hfour : Nat.card H = 4 := by
    have hcases : Nat.card H = 3 ∨ Nat.card H = 4 := by omega
    rcases hcases with hthree | hfour
    · norm_num [hthree] at hdvd
    · exact hfour
  exact (eq_of_le_of_card_ge hUK (by rw [hE,hfour])).ge

omit [Finite M] in
private theorem neighbor_centralizes_radius {x s y : Vertex R}
    (hx : color R x = false) (hy : color R y = false)
    (hxs : Adjacent R x s)
    (hsmall : (cosetGraph R).dist s y + 3 < geometry.b R) :
    V R s ≤ centralizer (V R y : Set (FreeAmalgam R)) := by
  apply Escape.PairingControl.Geometry.V_le_of_h_neighbors hx hxs
  intro d hds
  have hs : color R s = true := by
    have h := adjacent_color_ne R hxs
    cases he : color R s <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hds
    cases he : color R d <;> simp_all
  have hVQ : V R y ≤ Q R d := by
    apply V_le_Q_of_dist_add_two_lt R hy
    have hdy : (cosetGraph R).dist y d ≤ (cosetGraph R).dist y s + 1 := by
      have hh := (cosetGraph_connected R).dist_triangle (u := y) (v := s) (w := d)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
        (adjacent_symm R hds))] at hh
      exact hh
    rw [SimpleGraph.dist_comm (u := y) (v := s)] at hdy
    omega
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)).trans
    (centralizer_le hVQ)

omit [Finite M] in
private theorem neighbor_centralizes_Z {x s y : Vertex R}
    (hx : color R x = false) (hy : color R y = false)
    (hxs : Adjacent R x s)
    (hsmall : (cosetGraph R).dist s y + 1 < geometry.b R) :
    V R s ≤ centralizer (Z R y : Set (FreeAmalgam R)) := by
  apply Escape.PairingControl.Geometry.V_le_of_h_neighbors hx hxs
  intro d hds
  have hs : color R s = true := by
    have h := adjacent_color_ne R hxs
    cases he : color R s <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hds
    cases he : color R d <;> simp_all
  have hZQ : Z R d ≤ Q R y := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d y < geometry.b R
    have hh := (cosetGraph_connected R).dist_triangle (u := d) (v := s) (w := y)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds)] at hh
    omega
  exact hZQ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes y hy)))

/-- The all-rho displacement is contained in the first odd radius layer,
which centralizes the radius at e-4 by critical minimality. -/
theorem backward_displacement_centralizes_fourBeforeEndpoint
    (source : LocalSource L R)
    (hb : 4 < geometry.b R) {a c : Vertex R}
    (hd : (cosetGraph R).dist a c = 2)
    (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅Z R w.backward, Q R c⁆ ≤
      centralizer (V R (fourBeforeEndpoint w) : Set (FreeAmalgam R)) := by
  have hlen := w.path.length_eq_b
  let s := w.path.walk.getVert 1
  have hcs : Adjacent R c s := (cosetGraph_adj R _ _).mp
    (SimpleGraph.dist_eq_one_iff_adj.mp (w.path.dist_start (by omega)))
  have hZV : Z R w.backward ≤ V R c :=
    le_iSup_of_le w.backward (le_iSup_of_le (w.backward_distance hd).le le_rfl)
  apply ((commutator_mono hZV le_rfl).trans
    (radius_displacement_le_neighbor_of_triple source (by omega) w.path.start_color hcs
      (radius_triple_le_Z_at_any_center (by omega) w.path.start_color hall
        w.path.start_color))).trans
  apply neighbor_centralizes_radius w.path.start_color (fourBeforeEndpoint_color w) hcs
  have hseg := SimpleGraph.dist_le ((w.path.walk.drop 1).take (w.path.walk.length - 5))
  rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    SimpleGraph.Walk.drop_getVert] at hseg
  have hstep : 1 + (w.path.walk.length - 5) = w.path.walk.length - 4 := by omega
  rw [hstep] at hseg
  change (cosetGraph R).dist s (fourBeforeEndpoint w) + 3 < geometry.b R
  change (cosetGraph R).dist s (fourBeforeEndpoint w) ≤ _ at hseg
  omega

/-- The commutator at e-4 lies in the next odd radius layer and therefore
centralizes Z_e. -/
theorem fourBeforeEndpoint_commutator_centralizes_endpoint
    (source : LocalSource L R)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆, Z R w.endpoint⁆ = ⊥ := by
  have hlen := w.path.length_eq_b
  let s := w.path.walk.getVert (w.path.walk.length - 3)
  have hts : Adjacent R (fourBeforeEndpoint w) s := by
    have hh := w.path.walk.adj_getVert_succ (i := w.path.walk.length - 4) (by omega)
    have hstep : w.path.walk.length - 4 + 1 = w.path.walk.length - 3 := by omega
    rw [hstep] at hh
    exact (cosetGraph_adj R _ _).mp hh
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hbound : ⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆ ≤
      ⁅V R (fourBeforeEndpoint w), Q R (fourBeforeEndpoint w)⁆ := by
    rw [commutator_comm (Z R w.backward) (V R (fourBeforeEndpoint w))]
    exact commutator_mono le_rfl (backward_Z_le_fourBeforeEndpoint_kernel hb ha w)
  apply (hbound.trans
    (radius_displacement_le_neighbor_of_triple source (by omega) (fourBeforeEndpoint_color w)
      hts (radius_triple_le_Z_at_any_center (by omega) w.path.start_color hall
        (fourBeforeEndpoint_color w)))).trans
  apply neighbor_centralizes_Z (fourBeforeEndpoint_color w) w.path.end_color hts
  have hs := w.path.dist_end (w.path.walk.length - 3)
  change (cosetGraph R).dist s w.endpoint = _ at hs
  omega

/-- The second image bound captures the complete backward displacement.
The natural marking supplies its exact order and exact action kernel. -/
theorem backward_displacement_le_fourBeforeEndpoint_commutator
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hsecond : 2 < (Q R w.backward).relIndex (V R (fourBeforeEndpoint w))) :
    ⁅Z R w.backward, Q R c⁆ ≤ ⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆ := by
  let K := V R (fourBeforeEndpoint w)
  let E := ⁅Z R w.backward, Q R c⁆
  have hdcol := w.backward_color ha
  have hEU : E ≤ U R w.backward := displacement_le_U common hdcol (w.backward_distance hd)
  have hUcard := common.natural.card_at w.backward hdcol
  let : Finite (U R w.backward) := Nat.finite_of_card_ne_zero (by rw [hUcard]; decide)
  have hKS : K ≤ stabilizer R w.backward :=
    (fourBeforeEndpoint_V_le_center_kernel hb w).trans
      (Q_le_stabilizer_of_dist_two R c w.backward w.path.start_color
        (by rw [SimpleGraph.dist_comm]; exact w.backward_distance hd))
  let := finite_stabilizer R w.backward
  let : Finite K := Finite.of_injective (inclusion hKS) (inclusion_injective hKS)
  have hUK : ⁅U R w.backward, K⁆ ≤ E :=
    commutator_mono (U_le_Z R _) (fourBeforeEndpoint_V_le_center_kernel hb w)
  have hindex : 2 < (centralizer (U R w.backward : Set (FreeAmalgam R))).relIndex K := by
    have heq : (Q R w.backward).subgroupOf K =
        (centralizer (U R w.backward : Set (FreeAmalgam R))).subgroupOf K := by
      ext x
      change (x : FreeAmalgam R) ∈ Q R w.backward ↔ _
      rw [← common.natural.centralizer w.backward hdcol]
      exact and_iff_right (hKS x.property)
    change 2 < ((Q R w.backward).subgroupOf K).index at hsecond
    rw [heq] at hsecond
    exact hsecond
  exact (capture_index_two (U R w.backward) E K hEU
    (backward_displacement_card_four common hb ha hd w) hUcard
    (backward_displacement_centralizes_fourBeforeEndpoint source hb hd w hall) hUK hindex).trans
    (commutator_mono (U_le_Z R _) le_rfl)

/-- Both commutator conclusions in the all-rho paragraph, with the actual
second image bound still explicit for the source assembly owner. -/
theorem commutator_capture_and_endpoint_centrality
    (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hsecond : 2 < (Q R w.backward).relIndex (V R (fourBeforeEndpoint w))) :
    ⁅Z R w.backward, Q R c⁆ ≤ ⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆ ∧
      ⁅⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆, Z R w.endpoint⁆ = ⊥ :=
  ⟨backward_displacement_le_fourBeforeEndpoint_commutator common hb ha hd w hall hsecond,
    fourBeforeEndpoint_commutator_centralizes_endpoint source hb ha w hall⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
