module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges

/-!
# Centrality and intersections in the neighboring rigidity argument

The local center is the center of the full stabilizer. Intersecting the
Z-layer with the fixed core gives a subgroup of that center, using generation
by the local residual and the two-core. The fixed core alone is not identified
with the center.

For a moving neighbor, the order-four edge displacement is exactly the
intersection of its natural eight-group with the original Z-layer. Local
control makes that displacement central at the original vertex. Thus a
noncentral intersection forces nonmovement and containment in the genuine B.
Conversely two moving neighbors have a noncentral intersection, since their
common nontrivial displacement lies in the natural group at either vertex.

Source: Meierfrankenfeld--Stellmacher (1993), first and last paragraphs of
(4.3.4), printed p.886. The intervening local-action equality is not proved here.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual local center as an ambient intersection. -/
theorem localCenter_eq (a : Vertex R) :
    localCenter a = stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y y.property)

variable [Finite M]

/-- Centrality follows by centralizing both generators of the stabilizer. -/
theorem Z_inf_fixedCore_le_localCenter (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    Z R a ⊓ fixedCore R a ≤ localCenter a := by
  rw [localCenter_eq]
  refine le_inf (inf_le_left.trans (Z_le_stabilizer R a)) ?_
  apply le_centralizer_iff.mpr
  rw [← source.local_generation a ha]
  exact sup_le (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
    (le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))))

omit [Finite M] in
/-- The natural summand has no fixed points for the full local group. -/
theorem U_inf_localCenter_eq_bot (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : U R a ⊓ localCenter a = ⊥ := by
  apply le_bot_iff.mp
  rw [← EdgeTransfer.U_fixed_eq_bot modules a ha]
  rw [localCenter_eq]
  exact inf_le_inf_left _ (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer a)))

omit [Finite M] in
/-- Two neighbors of the same holomorph vertex have the M-color. -/
theorem neighbor_color {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t) : color R d = false := by
  have h₁ := adjacent_color_ne R hat
  have h₂ := adjacent_color_ne R hdt
  cases ht : color R t <;> cases hd : color R d <;> simp_all

variable (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)

include source hb p control edge in
/-- A moving edge displacement centralizes the entire original stabilizer. -/
theorem moving_displacement_le_localCenter
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    edgeDisplacement d t ≤ localCenter a := by
  have hdc := neighbor_color ha hat hdt
  have hZ : edgeDisplacement d t ≤ Z R a :=
    (edge_le_Z p hb control edge d t hdc hdt).trans (EdgeTransfer.edge_Z_le a t ha hat)
  have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le
    (show (cosetGraph R).dist d a ≤ 2 by rw [SimpleGraph.dist_comm, hd.1]) le_rfl)
  have hfixed : edgeDisplacement d t ≤ fixedCore R a := by
    rw [← (moving_edge_eq_at p (by omega) control a t d ha hat hdt hd).2,
      (moving_edge_eq_at p (by omega) control a t d ha hat hdt hd).1]
    exact (commutator_mono hdV le_rfl).trans
      (commutator_le_fixed_at p (by omega) control a ha)
  exact (le_inf hZ hfixed).trans (Z_inf_fixedCore_le_localCenter source a ha)

include hb modules p initial control edge in
/-- For a moving neighbor, the natural intersection is its edge displacement. -/
theorem moving_natural_intersection
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    U R d ⊓ Z R a = edgeDisplacement d t := by
  have hdc := neighbor_color ha hat hdt
  have heq := moving_edge_eq_at p (by omega) control a t d ha hat hdt hd
  have hcard := edge_card p (by omega) initial d t hdc hdt
  have hU := EdgeTransfer.edge_commutator_le_natural hb modules d t hdc hdt
  have hZ := (edge_le_Z p hb control edge d t hdc hdt).trans
    (EdgeTransfer.edge_Z_le a t ha hat)
  let C := U R d ⊓ Z R a
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at d hdc]; decide)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U R d from inf_le_left))
    (inclusion_injective _)
  have hle : edgeDisplacement d t ≤ C := le_inf hU hZ
  have hge : 4 ≤ Nat.card C := hcard ▸ card_le_of_le hle
  have hdvd : Nat.card C ∣ 8 := modules.natural.card_at d hdc ▸ card_dvd_of_le
    (show C ≤ U R d from inf_le_left)
  have hne : Nat.card C ≠ 8 := by
    intro hc
    have hCU : C = U R d := eq_of_le_of_card_ge inf_le_left
      (by rw [hc, modules.natural.card_at d hdc])
    have hUC : U R d ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
      (hCU ▸ (show C ≤ Z R a from inf_le_right)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))
    have hQa : Q R a ≤ stabilizer R d := Q_le_stabilizer_of_dist_two R a d ha hd.1
    let s : BinaryNaturalStructure source :=
      ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
    have hZC : Z R d ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
      rw [s.decomposition_at d hdc]
      exact sup_le hUC (inf_le_right.trans (centralizer_le hQa))
    have hbot : edgeDisplacement d t = ⊥ := by
      rw [← heq.2, heq.1]
      exact commutator_eq_bot_iff_le_centralizer.mpr hZC
    rw [hbot, card_bot] at hcard
    omega
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hCcard : Nat.card C = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hcard, hCcard])).symm

include hb modules p initial control edge in
/-- The first exclusion in (4.3.4), with the literal local-center condition. -/
theorem not_moving_of_noncentral_intersection
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hn : ¬ U R d ⊓ Z R a ≤ localCenter a) :
    d ∉ movingNeighbors geometry a := by
  intro hd
  apply hn
  rw [moving_natural_intersection hb modules p initial control edge a t d ha hat hdt hd]
  exact moving_displacement_le_localCenter (source := source) hb p control edge a t d ha hat hdt hd

include hb modules p initial control edge in
/-- Noncentrality forces the full neighboring Z-layer into B. -/
theorem Z_le_B_of_noncentral_intersection
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hn : ¬ U R d ⊓ Z R a ≤ localCenter a) :
    Z R d ≤ B R a (geometry.Z_normal a) := by
  by_cases heq : a = d
  · subst d
    exact EdgeTransfer.Z_le_B hb a ha
  · exact of_not_not fun h => not_moving_of_noncentral_intersection hb modules p initial control edge
      a t d ha hat hdt hn ⟨neighbor_distance_two ha hat hdt heq, h⟩

include hb modules p initial control in
/-- The common displacement of two moving neighbors witnesses noncentrality. -/
theorem moving_intersection_noncentral
    (a t d e : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (het : Adjacent R e t)
    (hd : d ∈ movingNeighbors geometry a) (he : e ∈ movingNeighbors geometry a) :
    ¬ U R d ⊓ Z R e ≤ localCenter e := by
  have hdc := neighbor_color ha hat hdt
  have hec := neighbor_color ha hat het
  have hde : edgeDisplacement d t = edgeDisplacement e t :=
    (moving_edge_eq_at p (by omega) control a t d ha hat hdt hd).2.symm.trans
      (moving_edge_eq_at p (by omega) control a t e ha hat het he).2
  have hUd := EdgeTransfer.edge_commutator_le_natural hb modules d t hdc hdt
  have hUe := EdgeTransfer.edge_commutator_le_natural hb modules e t hec het
  have hcard := edge_card p (by omega) initial e t hec het
  intro h
  have hcentral : edgeDisplacement e t ≤ localCenter e := by
    apply (show edgeDisplacement e t ≤ U R d ⊓ Z R e from
      le_inf (hde ▸ hUd) (hUe.trans (U_le_Z e))).trans h
  have hbot : edgeDisplacement e t = ⊥ := le_bot_iff.mp (by
    rw [← U_inf_localCenter_eq_bot modules e hec]
    exact le_inf hUe hcentral)
  rw [hbot, card_bot] at hcard
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
