module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Opposite.Choices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The two commutator calculations in MS93 step (6)

If [Z_mu,Z_fourth] lies in Z_d, conjugation by Z_fourth preserves
[Z_mu,Q_d]: Z_d centralizes Q_d and Z_fourth normalizes Q_d. Step (3)
identifies this commutator with the chosen edge plane. That plane has
index two in U_d, so its normalizer acts trivially on the quotient.
Consequently [U_d,Z_fourth] lies in the plane. The critical natural-layer
identity puts R_4 there as well, contrary to the choice of lambda.
This proves the printed obstruction even without assuming R_mu = 1.

For the first calculation, [Z_back,Z_endpoint] lies in Z_start precisely
when the critical commutator line lies in the selected edge plane. One
implication follows by normalizing [Z_back,Q_start]. Conversely, equal edge
planes give equal dual lines modulo B, so normalization of the edge plane
puts the commutator in B. Its commutator with Q_start is both contained in
the edge plane and normalized by the starting stabilizer; irreducibility
makes it trivial, and the elementary radius puts it in X_start = Z_start.

The original backward-choice condition permits both cases. The imported
choice constructions therefore give one choice with the printed
noncontainment and another with containment. The existential noncontainment
has no additional premise; the noncontainment for every original choice
is not established here. These diagnostics do not refute the full contrary
configuration, whose eventual exclusion remains the parent argument.

On printed p.885 the first target is Z_alpha, followed by a comma.
`backward_commutator_le_endpoint_Z` preserves the different endpoint
containment already forced by (4.3.1)(i).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.1)(i), printed p.882, and (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix

private theorem normalizes_commutator_of_central_bound
    {G : Type*} [Group G] (H Q Z A : Subgroup G)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hAQ : A ≤ normalizer (Q : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G)) (hHA : ⁅H, A⁆ ≤ Z) :
    A ≤ normalizer (⁅H, Q⁆ : Subgroup G) := by
  have hreduce := commutator_eq_of_centralizing_sup (B := Z ⊔ H) rfl hZQ hHQ
  apply le_normalizer_iff.mpr
  intro a ha k hk
  have hmap : H.map (MulAut.conj a).toMonoidHom ≤ Z ⊔ H := by
    rintro y ⟨x, hx, rfl⟩
    have hcomm : ⁅a, x⁆ ∈ Z := by
      apply hHA
      rw [commutator_comm]
      exact commutator_mem_commutator ha hx
    have hh := (Z ⊔ H).mul_mem (mem_sup_left hcomm) (mem_sup_right hx)
    change a * x * a⁻¹ ∈ Z ⊔ H
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hQmap : Q.map (MulAut.conj a).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hAQ ha)
  have hh := mem_map_of_mem (MulAut.conj a).toMonoidHom hk
  rw [map_commutator, hQmap] at hh
  have h := commutator_mono hmap (le_refl Q) hh
  rw [commutator_comm (Z ⊔ H), ← hreduce, commutator_comm] at h
  exact h

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The initial radius identity puts every backward-neighbor commutator
in Z_endpoint. Thus the first obstruction on p.885 must concern Z_start. -/
theorem backward_commutator_le_endpoint_Z (source : LocalSource L R)
    (p : Counterexample geometry) (hi : InitialFacts p) (choice : BackwardChoice p) :
    ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a' := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by have := hi.six_le; omega)
  have h := hi.radius_eq_edge t ht
  exact (commutator_mono (moving_Z_le_V choice.moving) le_rfl).trans
    (h.le.trans ((Initial.edge_le_natural source p.a' t p.end_color
      ht.endpoint_adjacent).trans (U_le_Z p.a')))

private theorem backward_endpoint_normalizes_edge_of_commutator_le_start_Z
    (hb : 2 < geometry.b R) (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p)
    (hbound : ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a) :
    Z R p.a' ≤ normalizer (edgeDisplacement p.a choice.edge : Set (FreeAmalgam R)) := by
  have hE : edgeDisplacement p.a choice.edge = ⁅Z R choice.back, Q R p.a⁆ :=
    (facts.edge_eq p.a choice.edge choice.back p.color_a choice.adjacent_start
      choice.adjacent_back choice.moving).symm.trans
      (FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
        p.a choice.edge choice.back p.color_a choice.adjacent_start
        choice.adjacent_back choice.moving).symm
  rw [hE]
  apply normalizes_commutator_of_central_bound _ _ (Z R p.a) _ _ _ _ hbound
  · exact ((moving_Z_le_V choice.moving).trans
      ((geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1))).trans
        (Q_normalized R p.a)
  · exact p.end_Z_le_start_stabilizer.trans (Q_normalized R p.a)
  · exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.a p.color_a)

/-- The printed start-Z obstruction for a choice avoiding the critical line.
The existence theorem below discharges this extra condition. -/
theorem backward_commutator_not_le_start_Z_of_critical_avoidance (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p)
    (havoid : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) :
    ¬ ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a := by
  intro hbound
  obtain ⟨hi⟩ := initial p
  exact havoid ((backwardChoice_endpoint_normalizes_iff source modules hi choice).mp
    (backward_endpoint_normalizes_edge_of_commutator_le_start_Z hb facts initial p bad choice hbound))

private theorem backward_fixed_summand_le_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {p : Counterexample geometry} (choice : BackwardChoice p) :
    Z R choice.back ⊓ centralizer (stabilizer R choice.back : Set (FreeAmalgam R)) ≤
      Z R p.a := by
  rw [← modules.X_eq_Z p.a p.color_a]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  have hZQ := (moving_Z_le_V choice.moving).trans (geometry.V_le_Q hb p.a p.color_a)
  let := geometry.Z_elementary (by omega) choice.back (moving_color p.color_a choice.moving)
  exact ⟨hZQ hx.1, elemPow_eq_one_of_isElementaryAbelian x hx.1,
    fun y hy => hx.2 y
      (Q_le_stabilizer_of_dist_two R p.a choice.back p.color_a choice.moving.1 hy)⟩

private theorem backward_commutator_le_start_Z_of_endpoint_normalizes_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p)
    (hn : Z R p.a' ≤ normalizer (edgeDisplacement p.a choice.edge : Set (FreeAmalgam R))) :
    ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a := by
  let E := edgeDisplacement p.a choice.edge
  let B₀ := B R p.a (geometry.Z_normal p.a)
  let S := stabilizer R p.a
  let H := Z R choice.back
  let A := Z R p.a'
  let K := ⁅H, A⁆
  have hBV : B₀ ≤ V R p.a := EdgeTransfer.B_le_radius hb p.a p.color_a
  have hVG : V R p.a ≤ S := (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hHV : H ≤ V R p.a := moving_Z_le_V choice.moving
  have hBG := hBV.trans hVG
  have hHG := hHV.trans hVG
  have hAG : A ≤ S := p.end_Z_le_start_stabilizer
  have hEU : E ≤ U R p.a := Initial.edge_le_natural source p.a choice.edge
    p.color_a choice.adjacent_start
  have hEZ : E ≤ Z R p.a := hEU.trans (U_le_Z _)
  have hAB : A ≤ normalizer (B₀ : Set (FreeAmalgam R)) :=
    hAG.trans (Selection.fixedPreimage_normalized hb p.a p.color_a)
  have hHB : A ≤ normalizer (H ⊔ B₀ : Subgroup (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    apply (show (H ⊔ B₀).map (MulAut.conj a).toMonoidHom ≤ H ⊔ B₀ from ?_)
      (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)
    have hBmap : B₀.map (MulAut.conj a).toMonoidHom = B₀ :=
      mem_normalizer_iff_map_conj_eq.mp (hAB ha)
    rw [Subgroup.map_sup, hBmap]
    apply sup_le _ le_sup_right
    have hfix : act R a⁻¹ p.a = p.a := (stabilizer R p.a).inv_mem (hAG ha)
    have hm := (FirstPairing.movingNeighbors_act_iff hb a⁻¹ p.a choice.back p.color_a).mpr
      choice.moving
    rw [hfix] at hm
    have hadj := (adjacent_act_iff R a⁻¹ p.a choice.edge).mpr choice.adjacent_start
    rw [hfix] at hadj
    have he : edgeDisplacement p.a (act R a⁻¹ choice.edge) = E := by
      have ht := FirstPairing.edgeDisplacement_act a⁻¹ p.a choice.edge
      rw [hfix, inv_inv] at ht
      exact ht.trans (mem_normalizer_iff_map_conj_eq.mp (hn ha))
    have hc := Selection.Six.Complement.moving_fixed_cover source hb modules initial facts
      bad p.color_a hadj ((adjacent_act_iff R a⁻¹ choice.back choice.edge).mpr
        choice.adjacent_back) choice.adjacent_start choice.adjacent_back hm choice.moving he
    have hz := Z_act R a⁻¹ choice.back
    simp only [inv_inv] at hz
    change H.map (MulAut.conj a).toMonoidHom ≤ H ⊔ B₀
    rw [← hz]
    exact hc
  have hindex : B₀.relIndex (H ⊔ B₀) = 2 := by
    let : Finite S := finite_stabilizer R p.a
    let : (B₀.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
      (Selection.fixedPreimage_normalized hb p.a p.color_a)
    let s : BinaryNaturalStructure source :=
      ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
    have hcover : H ⊔ B₀ = U R choice.back ⊔ B₀ := by
      apply le_antisymm _ (sup_le ((U_le_Z _).trans le_sup_left) le_sup_right)
      apply sup_le _ le_sup_right
      change Z R choice.back ≤ _
      rw [s.decomposition_at choice.back (moving_color p.color_a choice.moving)]
      exact sup_le le_sup_left ((backward_fixed_summand_le_start_Z source hb modules choice).trans
        ((EdgeTransfer.Z_le_B hb p.a p.color_a).trans le_sup_right))
    have hUG : U R choice.back ≤ S := (U_le_Z _).trans hHG
    have hi := relIndex_sup_right ((U R choice.back).subgroupOf S) (B₀.subgroupOf S)
    rw [← subgroupOf_sup hUG hBG, relIndex_subgroupOf (sup_le hUG hBG),
      relIndex_subgroupOf hUG, ← hcover] at hi
    rw [hi]
    have he := Continuation.moving_natural_intersection source hb modules facts p initial bad
      p.color_a choice.adjacent_start choice.adjacent_back choice.moving
    have hEback : E ≤ U R choice.back := he.ge.trans inf_le_left
    have hEB : E ≤ B₀ := hEZ.trans (EdgeTransfer.Z_le_B hb p.a p.color_a)
    let : Finite (U R choice.back) := Nat.finite_of_card_ne_zero (by
      rw [modules.natural.card_at _ (moving_color p.color_a choice.moving)]; decide)
    have hEindex : E.relIndex (U R choice.back) = 2 := by
      have hc := (E.subgroupOf (U R choice.back)).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hEback).toEquiv,
        FirstPairing.StepThree.edge_card p (by omega) initial p.a choice.edge p.color_a
          choice.adjacent_start,
        modules.natural.card_at _ (moving_color p.color_a choice.moving)] at hc
      change (E.subgroupOf (U R choice.back)).index = 2
      omega
    have hle := relIndex_le_of_le_left hEB
      (show E.relIndex (U R choice.back) ≠ 0 by rw [hEindex]; decide)
    have hpos := Nat.pos_of_ne_zero (B₀.subgroupOf (U R choice.back)).index_ne_zero_of_finite
    have hnot : B₀.relIndex (U R choice.back) ≠ 1 := by
      intro h
      apply choice.moving.2
      change H ≤ B₀
      exact le_sup_left.trans (hcover.le.trans (sup_le (relIndex_eq_one.mp h) le_rfl))
    rw [hEindex] at hle
    change 0 < B₀.relIndex (U R choice.back) at hpos
    omega
  have hKB : K ≤ B₀ :=
    (commutator_mono le_sup_left le_rfl).trans
      (commutator_le_of_normalized_index_two _ _ _ le_sup_right hindex hHB hAB)
  have hQnE : Q R p.a ≤ normalizer (E : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.a p.color_a))).trans
        ((centralizer_le hEZ).trans (Subgroup.centralizer_le_normalizer _))
  have hHE : ⁅H, Q R p.a⁆ ≤ E := by
    rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
      p.a choice.edge choice.back p.color_a choice.adjacent_start
      choice.adjacent_back choice.moving,
      facts.edge_eq p.a choice.edge choice.back p.color_a choice.adjacent_start
        choice.adjacent_back choice.moving]
  let W := commutatorPreimage (Q R p.a) (Q R p.a) E
  have hHW : H ≤ W := le_commutatorPreimage (hHV.trans (geometry.V_le_Q hb p.a p.color_a)) hHE
  have hAW : A ≤ normalizer (W : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ hQnE
      (hAG.trans (Q_normalized R p.a)) (hAG.trans (Q_normalized R p.a)) hn
  have hKW : K ≤ W := (commutator_mono hHW le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAW)
  have hKQ : ⁅K, Q R p.a⁆ ≤ E := (commutator_mono hKW le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hQnE)
  have hzero := Selection.edge_normal_subgroup_eq_bot source hb modules facts p.color_a
    choice.adjacent_start _ hKQ
    (FirstPairing.StepThree.fixed_subgroup_commutator_normalized source hb p.color_a hKB)
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hzero
  obtain ⟨hi⟩ := initial p
  let := Continuation.radius_elementary (show 4 < geometry.b R by have := hi.six_le; omega) p.color_a
  rw [← modules.X_eq_Z p.a p.color_a]
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨geometry.V_le_Q hb p.a p.color_a (hBV (hKB hx)),
    elemPow_eq_one_of_isElementaryAbelian x (hBV (hKB hx)), hcentral hx⟩

/-- The exact extra separation required of the original backward choice. -/
theorem backward_commutator_le_start_Z_iff (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p) :
    ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a ↔
      criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge := by
  obtain ⟨hi⟩ := initial p
  rw [← backwardChoice_endpoint_normalizes_iff source modules hi choice]
  exact ⟨backward_endpoint_normalizes_edge_of_commutator_le_start_Z hb facts initial p bad choice,
    backward_commutator_le_start_Z_of_endpoint_normalizes_edge source hb modules facts initial p bad choice⟩

/-- An actual original backward choice satisfying the printed first obstruction,
with critical avoidance constructed from the earlier inputs. -/
theorem exists_backwardChoice_commutator_not_le_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ choice : BackwardChoice p, ¬ ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a := by
  obtain ⟨choice, havoid⟩ := exists_backwardChoice_critical_avoidance
    source hb modules transfer facts initial p bad
  exact ⟨choice, backward_commutator_not_le_start_Z_of_critical_avoidance
    source hb modules facts initial p bad choice havoid⟩

/-- The original backward-choice contract also admits the opposite case.
This diagnoses the universal version of the printed obstruction; it does
not refute the full contrary hypotheses. -/
theorem exists_backwardChoice_commutator_le_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ choice : BackwardChoice p, ⁅Z R choice.back, Z R p.a'⁆ ≤ Z R p.a := by
  obtain ⟨choice, hcontain⟩ := exists_backwardChoice_critical_containment
    source hb modules transfer initial p bad
  exact ⟨choice, (backward_commutator_le_start_Z_iff
    source hb modules facts initial p bad choice).mpr hcontain⟩

namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

/-- The second printed obstruction in step (6), with the actual fourth
vertex and chosen endpoint d. The trivial-R_mu hypothesis is unnecessary. -/
theorem mu_fourth_commutator_not_le_endpoint_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) : ¬ ⁅Z R w.mu, Z R w.fourth⁆ ≤ Z R d := by
  intro hbound
  have hdc := endpoint_color hd
  let E := edgeDisplacement d w.lam
  have hE : E = ⁅Z R w.mu, Q R d⁆ :=
    (facts.edge_eq d w.lam w.mu hdc w.lam_adjacent w.mu_adjacent w.mu_moving).symm.trans
      (FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
        initial bad d w.lam w.mu hdc w.lam_adjacent w.mu_adjacent w.mu_moving).symm
  have hEU : E ≤ U R d := Initial.edge_le_natural source d w.lam hdc w.lam_adjacent
  have hfour := FirstPairing.StepThree.edge_card p (by omega) initial
    d w.lam hdc w.lam_adjacent
  have hAS : Z R w.fourth ≤ stabilizer R d :=
    (source.critical_Z_le_stabilizer geometry w.fourth w.fourth_color d w.critical).1
  have hn : Z R w.fourth ≤ normalizer (E : Set (FreeAmalgam R)) := by
    rw [hE]
    apply normalizes_commutator_of_central_bound _ _ (Z R d) _ _ _ _ hbound
    · exact ((moving_Z_le_V w.mu_moving).trans
        ((geometry.V_le_Q hb d hdc).trans (fun _ hx => hx.1))).trans (Q_normalized R d)
    · exact hAS.trans (Q_normalized R d)
    · exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at d hdc]; decide)
  have hindex : E.relIndex (U R d) = 2 := by
    have hecard : Nat.card (E.subgroupOf (U R d)) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv).trans hfour
    have hh := (E.subgroupOf (U R d)).index_mul_card
    rw [hecard, modules.natural.card_at d hdc] at hh
    change (E.subgroupOf (U R d)).index = 2
    omega
  have hcomm : ⁅U R d, Z R w.fourth⁆ ≤ E :=
    commutator_le_of_normalized_index_two _ _ _ hEU hindex
      (hAS.trans (U_normalized d)) hn
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  apply w.escapes
  change ⁅Z R w.fourth, Z R d⁆ ≤ E
  rw [s.critical_commutator_eq geometry w.fourth w.fourth_color d w.critical,
    commutator_comm]
  exact (commutator_mono le_rfl (U_le_Z w.fourth)).trans hcomm

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
