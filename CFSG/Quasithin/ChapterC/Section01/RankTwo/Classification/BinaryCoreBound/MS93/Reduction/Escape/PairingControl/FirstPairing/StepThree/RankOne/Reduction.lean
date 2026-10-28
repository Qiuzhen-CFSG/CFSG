module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Normalization
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Consequences
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Reducing the alpha identification to natural-subgroup containment

The moving commutator K is an elementary four-group in the actual fixed
preimage B_alpha. The delta-side edge equality makes Q_t normalize K.
If K ≤ U_alpha, then K has index two in U_alpha, so Q_t acts trivially on
U_alpha/K. Thus the alpha-side displacement lies in K; both have order four.

This finishes the edge identification once the rank-one representation
argument places K in U_alpha. It neither assumes that identification nor
uses the later equality H = U. Source: MS93 (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The section's triple bound places the whole moving commutator in B. -/
theorem moving_commutator_le_B (hb : 2 < geometry.b R)
    {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) (o : MovingOrientationAt a) :
    ⁅Z R d, Q R a⁆ ≤ B R a (geometry.Z_normal a) := by
  let S := stabilizer R a
  let := o.natural_section.normal_group
  let := o.natural_section.normal_kernel
  have hV : V R a ≤ S := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hQ : Q R a ≤ S := fun _ hx => hx.1
  have hcomm : ⁅V R a, Q R a⁆ =
      (⁅(V R a).subgroupOf S, (Q R a).subgroupOf S⁆).map S.subtype := by
    rw [map_commutator, map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hQ]
  apply (commutator_mono (moving_Z_le_V hd) le_rfl).trans
  rw [hcomm]
  rintro x ⟨y, hy, rfl⟩
  apply mem_map_of_mem S.subtype
  apply mem_centralizerModulo_iff.mpr
  refine ⟨commutator_le_left _ _ hy, ?_⟩
  intro l hl
  apply o.natural_section.triple_le
  rw [commutator_comm]
  exact commutator_mem_commutator hl hy

theorem moving_commutator_elementary (source : LocalSource L R)
    (modules : ModuleFacts source geometry) {a d : Vertex R}
    (ha : color R a = false) (hd : d ∈ movingNeighbors geometry a) :
    IsElementaryAbelian 2 (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  let : IsElementaryAbelian 2 (Z R d) := by
    rw [← modules.X_eq_Z d (moving_color ha hd)]
    exact omegaCenter_elementary _
  exact IsElementaryAbelian.of_le (le_normalizer_iff_commutator_le_left.mp
    ((Q_le_stabilizer_of_dist_two R a d ha hd.1).trans (Z_normalized R d)))

omit [Finite M] in
/-- The delta-side equality gives the actual edge actor's normalization. -/
theorem moving_commutator_normalized_edge (p : Counterexample geometry)
    (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    Q R t ≤ normalizer (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  rw [moving_commutator_eq_edge_at p hb initial bad a t d ha hat hdt hd]
  exact normalizer_commutator_ge_right _ _

/-- The edge actor fixes the neighbor image modulo the original radical.
The opposite coordinates must still convert this into line-residual fixation. -/
theorem moving_neighbor_fixed_mod_radical_by_edge (p : Counterexample geometry)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    ⁅(Z R d).subgroupOf (stabilizer R a), (Q R t).subgroupOf (stabilizer R a)⁆ ≤
      radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
        ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) := by
  let S := stabilizer R a
  have hQa : Q R a ≤ S := fun _ hx => hx.1
  have hV : V R a ≤ S := (geometry.V_le_Q hb a ha).trans hQa
  have hQt : Q R t ≤ S := fun _ hx => hx.2 a (adjacent_symm R hat)
  apply (map_le_map_iff_of_injective S.subtype_injective).mp
  rw [map_commutator, map_subgroupOf_eq_of_le ((moving_Z_le_V hd).trans hV),
    map_subgroupOf_eq_of_le hQt, radicalPreimage, Subgroup.map_sup, map_commutator,
    map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hQa,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)]
  change edgeDisplacement d t ≤ Z R a ⊔ ⁅V R a, Q R a⁆
  rw [← moving_commutator_eq_edge_at p (by omega) initial bad a t d ha hat hdt hd]
  exact (commutator_mono (moving_Z_le_V hd) le_rfl).trans le_sup_right

/-- Natural-subgroup containment suffices for the exact alpha-side equality.
The index-two action argument also works at any transported incident edge. -/
theorem alpha_commutator_of_le_U (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a)
    (hKU : ⁅Z R d, Q R a⁆ ≤ U R a) :
    ⁅Z R d, Q R a⁆ = edgeDisplacement a t := by
  let K := ⁅Z R d, Q R a⁆
  have hc : Nat.card K = 4 := moving_commutator_card_at p (by omega)
    initial bad a t d ha hat hdt hd
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  have hKUcard : Nat.card (K.subgroupOf (U R a)) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKU).toEquiv).trans hc
  have hi : K.relIndex (U R a) = 2 := by
    have hh := (K.subgroupOf (U R a)).index_mul_card
    rw [hKUcard, modules.natural.card_at a ha] at hh
    change (K.subgroupOf (U R a)).index = 2
    omega
  have hQG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hle : edgeDisplacement a t ≤ K := by
    change ⁅Z R a, Q R t⁆ ≤ K
    rw [EdgeTransfer.edge_commutator_eq_natural hb modules a t ha hat]
    exact commutator_le_of_normalized_index_two _ _ _ hKU hi
      (hQG.trans (U_normalized a))
      (moving_commutator_normalized_edge p (by omega) initial bad a t d ha hat hdt hd)
  exact (eq_of_le_of_card_ge hle (by
    rw [hc, edge_card p (by omega) initial a t ha hat])).symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree
