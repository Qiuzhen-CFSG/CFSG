module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic

/-!
# Reduction of Z-layer rigidity to one edge-action identity

Faithfulness of the marked natural action identifies neighboring two-cores
when one centralizes the other Z-layer; their omega-centers then agree.
This also handles containment of the whole natural summand. Otherwise the
natural intersection is the order-four edge displacement.

If neighboring edge displacements agree, local control puts their kernel
commutator in the fixed core and in the natural summand, forcing it to vanish.
Together with Basic's exclusion of movement, this reduces the first assertion
of (4.3.4) to the nonmoving edge-action identity stated explicitly below.
That identity remains a separate proof obligation, not a source assumption.

Source: Meierfrankenfeld--Stellmacher (1993), (4.1)(i), (4.3.3), and the
middle paragraph of (4.3.4), printed pp.881,886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A centralizing neighboring kernel has the same natural-action kernel and Z-layer. -/
theorem Z_eq_of_commutator_eq_bot (modules : ModuleFacts source geometry)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hc : ⁅Z R d, Q R a⁆ = ⊥) : Z R d = Z R a := by
  by_cases heq : a = d
  · exact congrArg (Z R) heq.symm
  have hdc := neighbor_color ha hat hdt
  have hQa : Q R a ≤ stabilizer R d :=
    Q_le_stabilizer_of_dist_two R a d ha (neighbor_distance_two ha hat hdt heq)
  have hle : Q R a ≤ Q R d := by
    rw [← modules.natural.centralizer d hdc]
    exact le_inf hQa ((le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc)).trans (centralizer_le (U_le_Z d)))
  let := finite_stabilizer R d
  let : Finite (Q R d) := Finite.of_injective
    (inclusion (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)) (inclusion_injective _)
  have hQ : Q R a = Q R d := eq_of_le_of_card_ge hle
    (by rw [source.Q_card a ha, source.Q_card d hdc])
  rw [← modules.X_eq_Z a ha, ← modules.X_eq_Z d hdc, X, X, hQ]

/-- Containing the whole neighboring natural group identifies the two Z-layers. -/
theorem Z_eq_of_U_le_Z (modules : ModuleFacts source geometry)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hU : U R d ≤ Z R a) : Z R d = Z R a := by
  by_cases heq : a = d
  · exact congrArg (Z R) heq.symm
  have hdc := neighbor_color ha hat hdt
  have hQa : Q R a ≤ stabilizer R d :=
    Q_le_stabilizer_of_dist_two R a d ha (neighbor_distance_two ha hat hdt heq)
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  apply Z_eq_of_commutator_eq_bot modules a t d ha hat hdt
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [s.decomposition_at d hdc]
  exact sup_le (hU.trans
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))
    (inf_le_right.trans (centralizer_le hQa))

/-- Distinct neighboring Z-layers intersect the natural group in the edge displacement. -/
theorem natural_intersection_of_Z_ne
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hne : Z R d ≠ Z R a) :
    U R d ⊓ Z R a = edgeDisplacement d t := by
  have hdc := neighbor_color ha hat hdt
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
  have hne8 : Nat.card C ≠ 8 := by
    intro hc
    have hCU : C = U R d := eq_of_le_of_card_ge inf_le_left
      (by rw [hc, modules.natural.card_at d hdc])
    exact hne (Z_eq_of_U_le_Z modules a t d ha hat hdt
      (hCU ▸ (show C ≤ Z R a from inf_le_right)))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hCcard : Nat.card C = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hcard, hCcard])).symm

/-- Equal edge displacements force equality of the full Z-layers. -/
theorem Z_eq_of_displacement_eq
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) (control : ∀ q : Counterexample geometry, LocalControl q)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (heq : edgeDisplacement d t = edgeDisplacement a t) :
    Z R d = Z R a := by
  by_cases had : a = d
  · exact congrArg (Z R) had.symm
  have hdist := neighbor_distance_two ha hat hdt had
  have htc : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all
  have hCedge : ⁅Z R d, Q R a⁆ ≤ edgeDisplacement d t :=
    commutator_mono le_rfl (Q_le_adjacent_h R htc hat)
  have hCU : ⁅Z R d, Q R a⁆ ≤ U R a := by
    rw [heq] at hCedge
    exact hCedge.trans (EdgeTransfer.edge_commutator_le_natural hb modules a t ha hat)
  have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le
    (show (cosetGraph R).dist d a ≤ 2 by rw [SimpleGraph.dist_comm, hdist]) le_rfl)
  have hfixed := (commutator_mono hdV (le_refl (Q R a))).trans
    (commutator_le_fixed_at p (by omega) control a ha)
  apply Z_eq_of_commutator_eq_bot modules a t d ha hat hdt
  apply le_bot_iff.mp
  rw [← EdgeTransfer.U_fixed_eq_bot modules a ha]
  exact le_inf hCU (hfixed.trans inf_le_right)

/-- The only remaining local-action step needed for the neighboring equality.
This conditional reduction does not assert that the displacement premise holds. -/
theorem equal_Z_of_nonmoving_displacement
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (displacement : ∀ a t d, color R a = false → Adjacent R a t → Adjacent R d t →
      Z R d ≤ B R a (geometry.Z_normal a) →
      ¬ edgeDisplacement d t ≤ localCenter a →
      edgeDisplacement d t = edgeDisplacement a t)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hn : ¬ U R d ⊓ Z R a ≤ localCenter a) :
    Z R d = Z R a := by
  by_cases heq : Z R d = Z R a
  · exact heq
  have hinter := natural_intersection_of_Z_ne hb modules p initial control edge a t d ha hat hdt heq
  have hB := Z_le_B_of_noncentral_intersection hb modules p initial control edge a t d ha hat hdt hn
  have hnedge : ¬ edgeDisplacement d t ≤ localCenter a := by rwa [hinter] at hn
  exact Z_eq_of_displacement_eq hb modules p control a t d ha hat hdt
    (displacement a t d ha hat hdt hB hnedge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
