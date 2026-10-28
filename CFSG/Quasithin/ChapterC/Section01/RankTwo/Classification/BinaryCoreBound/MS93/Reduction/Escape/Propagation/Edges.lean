module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.IndexTwo

/-!
# The two edge indices in MS93 (4.3.3)

Local control places the moving-neighbor displacements in the quotient-fixed
preimage B. The other displacements already lie there by nonmovement, so
(4.2)(i) places the original displacement in the edge Z-layer. Transport of
(4.3.1)(i) gives its order four at every edge. It is therefore the fixed plane
in the natural group of order eight. The central supplement transfers its
index to Z, and evaluation on the natural group computes the actor index.

The finite-group arithmetic is adapted from DistanceFour/Early/EdgeStructure/
Basic, with only ModuleFacts as input. The imported IndexTwo lemma is a general
abelian-action theorem importing only Mathlib; no distance-four source result
or CommonFacts is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.3), printed p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
open EdgeTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Distinct M-neighbors of one holomorph vertex are exactly two apart. -/
theorem neighbor_distance_two {a t d : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hne : a ≠ d) : (cosetGraph R).dist a d = 2 := by
  have hd : color R d = false := by
    have h₁ := adjacent_color_ne R hat
    have h₂ := adjacent_color_ne R hdt
    cases ht : color R t <;> cases hd : color R d <;> simp_all
  have hlow := (cosetGraph_connected R).one_lt_dist_of_ne_of_not_adj hne (by
    intro h
    exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp h)) (ha.trans hd.symm))
  have hupp := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := d)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat),
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))] at hupp
  omega

variable [Finite M]

/-- The fixed-core bound puts H in the actual quotient-fixed preimage B. -/
theorem H_le_B {p : Counterexample geometry} (hb : 2 < geometry.b R)
    (control : LocalControl p) : H R p.a ≤ B R p.a (geometry.Z_normal p.a) := by
  have hV : V R p.a ≤ stabilizer R p.a :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hcomm : ⁅V R p.a, Q R p.a⁆ ≤ V R p.a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R p.a ≤ stabilizer R p.a from fun _ hx => hx.1).trans (V_normalized p.a))
  have hcirc : Vcirc R p.a ≤ V R p.a :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer p.a).trans (V_normalized p.a))
  have hH : H R p.a ≤ ⁅V R p.a, Q R p.a⁆ := commutator_mono hcirc le_rfl
  intro x hx
  apply (mem_B_iff R p.a (geometry.Z_normal p.a) hV x).mpr
  refine ⟨hcomm (hH hx), fun l hl => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr ((control.commutator_le_fixed (hH hx)).2 l hl)]
  exact (Z R p.a).one_mem

/-- The first paragraph of (4.3.3): all neighboring displacements lie in B. -/
theorem neighbor_displacement_le_B {p : Counterexample geometry} (hb : 2 < geometry.b R)
    (control : LocalControl p) (t : Vertex R) (ht : Before p.a' p.a t 1)
    (d : Vertex R) (hdt : Adjacent R d t) :
    edgeDisplacement d t ≤ B R p.a (geometry.Z_normal p.a) := by
  by_cases hd : d ∈ movingNeighbors geometry p.a
  · rw [← (control.H_eq_edge t ht d hdt hd).2]
    exact H_le_B hb control
  · have hZ : Z R d ≤ B R p.a (geometry.Z_normal p.a) := by
      by_cases heq : p.a = d
      · subst d
        exact Z_le_B hb p.a p.color_a
      · have hdist := neighbor_distance_two p.color_a ht.endpoint_adjacent hdt heq
        exact of_not_not (fun h => hd ⟨hdist, h⟩)
    exact (le_normalizer_iff_commutator_le_left.mp
      ((show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
        (Z_normalized R d))).trans hZ

/-- Apply the preceding source edge transfer, now with all its premises proved. -/
theorem edge_le_Z_of_before {p : Counterexample geometry} (hb : 2 < geometry.b R)
    (control : LocalControl p) (edge : EdgeTransfer geometry)
    (t : Vertex R) (ht : Before p.a' p.a t 1) : edgeDisplacement p.a t ≤ Z R t :=
  edge p.a t p.color_a ht.endpoint_adjacent (neighbor_displacement_le_B hb control t ht)

/-- The displacement containment holds at every edge by transporting the
contrary configuration before applying local control. -/
theorem edge_le_Z (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    edgeDisplacement a t ≤ Z R t := by
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p (by omega) a t ha hat
  simpa only [hqa] using edge_le_Z_of_before hb (control q) edge t hqt

variable (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
include hb modules

/-- The central supplement transfers the fixed index from Z to its natural summand. -/
theorem edge_Z_index_eq_natural
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    (Z R b).relIndex (Z R a) = (Z R b).relIndex (U R a) := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hfixed : Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) ≤ Z R b := by
    rw [edge_Z_eq_fixed hb modules a b ha hab]
    exact inf_le_inf_left _ (centralizer_le hQ)
  have hcover : U R a ⊔ Z R b = Z R a := by
    apply le_antisymm (sup_le (U_le_Z a) (edge_Z_le a b ha hab))
    conv_lhs => rw [naturalData.decomposition_at a ha]
    exact sup_le le_sup_left (hfixed.trans le_sup_right)
  let K := (Z R b).subgroupOf (Z R a)
  let A := (U R a).subgroupOf (Z R a)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (((edge_Z_le_Q hb a b ha hab).trans (show Q R b ≤ stabilizer R b from
      fun _ hx => hx.1)).trans (Z_normalized R b))
  have hsup : A ⊔ K = ⊤ := by
    have hh := congrArg (fun H : Subgroup (FreeAmalgam R) => H.subgroupOf (Z R a)) hcover
    simpa only [subgroupOf_sup (U_le_Z a) (edge_Z_le a b ha hab), subgroupOf_self] using hh
  have hh := relIndex_sup_right A K
  rw [hsup, relIndex_top_right, relIndex_subgroupOf (U_le_Z a)] at hh
  exact hh

/-- Order-four edge displacement is precisely the fixed plane of the natural group. -/
theorem edge_fixed_natural_eq_commutator
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    U R a ⊓ Z R b = ⁅Z R a, Q R b⁆ := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at a ha]; decide)
  let C := U R a ⊓ Z R b
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U R a from inf_le_left))
    (inclusion_injective _)
  have hKC : ⁅Z R a, Q R b⁆ ≤ C := le_inf (edge_commutator_le_natural hb modules a b ha hab) hZ
  have hCge : 4 ≤ Nat.card C := hcard ▸ card_le_of_le hKC
  have hdvd : Nat.card C ∣ 8 := modules.natural.card_at a ha ▸ card_dvd_of_le
    (show C ≤ U R a from inf_le_left)
  have hne : Nat.card C ≠ 8 := by
    intro h
    have heq : C = U R a := eq_of_le_of_card_ge inf_le_left
      (by rw [h, modules.natural.card_at a ha])
    have hfix : U R a ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
      have hh : U R a ≤ Z R b := heq ▸ (show C ≤ Z R b from inf_le_right)
      rw [edge_Z_eq_fixed hb modules a b ha hab] at hh
      exact hh.trans inf_le_right
    apply edge_commutator_ne_bot modules a b ha hab
    rw [edge_commutator_eq_natural hb modules a b ha hab]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  have hdiv : Nat.card C ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hCcard : Nat.card C = 4 := by omega
  exact (eq_of_le_of_card_ge hKC (by rw [hCcard, hcard])).symm

/-- The fixed plane has index two in the actual natural group. -/
theorem edge_natural_index_of_card
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Z R b).relIndex (U R a) = 2 := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at a ha]; decide)
  have hfix := edge_fixed_natural_eq_commutator hb modules a b ha hab hZ hcard
  have hF : (Z R b).subgroupOf (U R a) = (⁅Z R a, Q R b⁆).subgroupOf (U R a) := by
    rw [← hfix]
    ext x
    simp only [mem_subgroupOf, mem_inf, x.property, true_and]
  have hFcard : Nat.card ((Z R b).subgroupOf (U R a)) = 4 := by
    rw [hF, Nat.card_congr (subgroupOfEquivOfLe
      (edge_commutator_le_natural hb modules a b ha hab)).toEquiv, hcard]
  have hh := ((Z R b).subgroupOf (U R a)).card_mul_index
  rw [hFcard, modules.natural.card_at a ha] at hh
  change 4 * (Z R b).relIndex (U R a) = 8 at hh
  omega

/-- The source Z-index follows from containment and displacement order four. -/
theorem edge_Z_index_of_card
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Z R b).relIndex (Z R a) = 2 := by
  rw [edge_Z_index_eq_natural hb modules a b ha hab]
  exact edge_natural_index_of_card hb modules a b ha hab hZ hcard

/-- Evaluation of the genuine edge action gives the second index in (4.3.3). -/
theorem edge_Q_index_of_card
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Q R a).relIndex (Q R b) = 4 := by
  let := geometry.U_elementary (lt_trans (by decide : 0 < 2) hb) a ha
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hfixed : U R a ⊓ centralizer (Q R b : Set (FreeAmalgam R)) = U R a ⊓ Z R b := by
    rw [edge_Z_eq_fixed hb modules a b ha hab, ← inf_assoc, inf_eq_left.mpr (U_le_Z a)]
  have hi : (U R a ⊓ centralizer (Q R b : Set (FreeAmalgam R))).relIndex (U R a) = 2 := by
    rw [hfixed, inf_relIndex_left]
    exact edge_natural_index_of_card hb modules a b ha hab hZ hcard
  have hc : ⁅U R a, Q R b⁆ ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
    rw [← edge_commutator_eq_natural hb modules a b ha hab]
    rw [edge_Z_eq_fixed hb modules a b ha hab] at hZ
    exact hZ.trans inf_le_right
  have hindex := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two (U R a) (Q R b)
    (hQ.trans (U_normalized a)) hc hi
  rw [← edge_commutator_eq_natural hb modules a b ha hab, hcard] at hindex
  have hkernel : (Q R a).subgroupOf (Q R b) =
      (centralizer (U R a : Set (FreeAmalgam R))).subgroupOf (Q R b) := by
    ext x
    change (x : FreeAmalgam R) ∈ Q R a ↔ (x : FreeAmalgam R) ∈ centralizer (U R a : Set (FreeAmalgam R))
    rw [← modules.natural.centralizer a ha, mem_inf]
    exact and_iff_right (hQ x.property)
  change ((Q R a).subgroupOf (Q R b)).index = 4
  rw [hkernel]
  exact hindex

/-- Both literal binary indices in MS93 (4.3.3). The result holds at every
oriented edge, with no need to put that edge on the original critical path. -/
theorem edge_indices (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    (Z R t).relIndex (Z R a) = 2 ∧ (Q R a).relIndex (Q R t) = 4 := by
  have hZ := edge_le_Z p hb control edge a t ha hat
  have hc := edge_card p (by omega) initial a t ha hat
  exact ⟨edge_Z_index_of_card hb modules a t ha hat hZ hc,
    edge_Q_index_of_card hb modules a t ha hat hZ hc⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
