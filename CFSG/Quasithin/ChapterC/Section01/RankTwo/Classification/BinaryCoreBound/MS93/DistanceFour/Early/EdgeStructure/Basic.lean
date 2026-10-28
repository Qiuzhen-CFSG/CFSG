module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.IndexTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.Commutator.ConjugateGeneration

/-!
# Binary edge arithmetic from containment and noncyclic displacement

The fixed summand of Z_alpha contributes no edge displacement, so the actual
edge commutator lies in the natural group U_alpha of order eight. Its
nontriviality follows from the faithful amalgam: a trivial action would make
the two adjacent kernels equal and normal in both vertex groups.

If the edge commutator is contained in Z_beta, its order is two or four.
In the order-four case it is exactly U_alpha intersect Z_beta. The natural
fixed subgroup then has index two. The central complement transports this
index to Z_alpha, and evaluation outside the fixed subgroup computes the
actor index using the actual kernel Q_alpha. Finally, edge containment at
all edges bounds the commutator of every radius-two generator with Q_alpha.

These are conditional steps toward MS93 (1993), (4.6.4)--(4.6.6), pp.902--903.
This file does not prove edge containment or exclude the order-two case;
those source arguments remain necessary before constructing EdgeFacts.
All finiteness is local to U_alpha, never imposed on the free amalgam.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem common_neighbor (t a : Vertex R) (hd : (cosetGraph R).dist t a = 2) :
    ∃ b, Adjacent R t b ∧ Adjacent R a b := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
  cases p with
  | nil => simp_all
  | @cons t b a htb p =>
    cases p with
    | nil => simp_all
    | @cons b c a hbc p =>
      have hp0 : p.length = 0 := by simp only [SimpleGraph.Walk.length_cons, hd] at hp; omega
      have heq : c = a := (SimpleGraph.Walk.length_eq_zero_iff.mp hp0).eq
      subst c
      exact ⟨b, (cosetGraph_adj R _ _).mp htb,
        adjacent_symm R ((cosetGraph_adj R _ _).mp hbc)⟩

include common

/-- The critical-distance bound places the adjacent Z-layer in the edge kernel. -/
theorem edge_Z_le_Q (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : Z R a ≤ Q R b := by
  apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
  rw [geometry.distance_constant a ha,
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)]
  exact lt_trans (by decide : 1 < 2) common.large_distance

/-- Edge containment bounds the radius commutator, by its distance-two generators. -/
theorem commutator_le_Z_of_edge [Finite M]
    (hedge : ∀ a b, color R a = false → Adjacent R a b → ⁅Z R a, Q R b⁆ ≤ Z R b)
    (a : Vertex R) (ha : color R a = false) : ⁅V R a, Q R a⁆ ≤ Z R a := by
  have hgen (t : Vertex R) (ht : (cosetGraph R).dist t a ≤ 2) :
      ⁅Z R t, Q R a⁆ ≤ Z R a := by
    have hta : (cosetGraph R).dist t a = 0 ∨
        (cosetGraph R).dist t a = 1 ∨ (cosetGraph R).dist t a = 2 := by omega
    rcases hta with hzero | hone | htwo
    · have heq : t = a := ((cosetGraph_connected R t a).dist_eq_zero_iff).mp hzero
      subst t
      rw [geometry.centralizes a ha]
      exact bot_le
    · have hat := adjacent_symm R
        ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hone))
      exact (commutator_mono (edge_Z_le a t ha hat) le_rfl).trans
        (by rw [geometry.centralizes a ha]; exact bot_le)
    · obtain ⟨b, htb, hab⟩ := common_neighbor t a htwo
      have hb : color R b = true := by
        have hh := adjacent_color_ne R hab
        cases hc : color R b <;> simp_all
      have htcol : color R t = false := by
        have hh := adjacent_color_ne R htb
        cases hc : color R t <;> simp_all
      exact (commutator_mono le_rfl (Q_le_adjacent_h R hb hab)).trans
        ((hedge t b htcol htb).trans (edge_Z_le a b ha hab))
  have hle (t : Vertex R) : (⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t) ≤ Q R a :=
    (le_iSup (fun t => ⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t) t).trans
      (radius_le_Q common a ha)
  change ⁅⨆ t, ⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t, Q R a⁆ ≤ Z R a
  rw [commutator_iSup_of_le _ _ hle]
  apply iSup_le
  intro t
  rw [commutator_iSup_of_le _ _ (fun ht =>
    (le_iSup (fun _ : (cosetGraph R).dist t a ≤ 2 => Z R t) ht).trans (hle t))]
  exact iSup_le fun ht => hgen t ht

/-- The central fixed summand contributes no edge displacement. -/
theorem edge_commutator_eq_natural [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ = ⁅U R a, Q R b⁆ := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hZa := edge_Z_le_Q common a b ha hab
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (naturalData.decomposition_at a ha).symm)
    (inf_le_right.trans (centralizer_le hQ))
    ((U_le_Z a).trans (hZa.trans (Q R b).le_normalizer))
  rw [commutator_comm, ← hh, commutator_comm]

/-- All edge displacement lies in the actual marked natural subgroup. -/
theorem edge_commutator_le_natural [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≤ U R a := by
  rw [edge_commutator_eq_natural common a b ha hab]
  exact le_normalizer_iff_commutator_le_left.mp
    ((show Q R b ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hab)).trans
      (U_normalized a))

/-- A trivial edge action would give a nontrivial common normal edge kernel. -/
theorem edge_commutator_ne_bot [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≠ ⊥ := by
  intro hbot
  have hcentral : Q R b ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot)
  have heq : Q R b = Q R a := by
    rw [← common.centralizer a b ha hab, inf_eq_left.mpr hcentral]
  have hQa : Q R a = ⊥ := by
    apply no_common_normal_at_edge R source.characteristic a b ha hab (Q R a)
    · exact le_inf (fun _ hx => hx.1) (fun _ hx => hx.2 b hab)
    · exact Q_normal R a
    · rw [← heq]
      exact Q_normal R b
  have hU : U R a = ⊥ := by
    apply le_bot_iff.mp
    have hZ : Z R a ≤ Q R a := by
      rw [← common.X_eq_Z a ha]
      exact omegaCenter_le _
    exact hQa ▸ (U_le_Z a).trans hZ
  have hc := common.natural.card_at a ha
  rw [hU, Nat.card_eq_fintype_card] at hc
  simp at hc

/-- Quadratic edge displacement has order two or four in the binary natural group. -/
theorem edge_commutator_card_two_or_four [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2 ∨
      Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  have hU := edge_commutator_le_natural common a b ha hab
  let : Finite (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective hU)
  have hdvd := card_dvd_of_le hU
  rw [common.natural.card_at a ha] at hdvd
  have hlarge : 1 < Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr (edge_commutator_ne_bot common a b ha hab)
  have hne : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≠ 8 := by
    intro hcard
    have heq : ⁅Z R a, Q R b⁆ = U R a :=
      eq_of_le_of_card_ge hU (by rw [common.natural.card_at a ha, hcard])
    have hfix : U R a ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
      rw [edge_Z_eq_fixed common a b ha hab] at hZ
      exact heq ▸ hZ.trans inf_le_right
    have hzero : ⁅Z R a, Q R b⁆ = ⊥ := by
      rw [edge_commutator_eq_natural common a b ha hab]
      exact commutator_eq_bot_iff_le_centralizer.mpr hfix
    exact edge_commutator_ne_bot common a b ha hab hzero
  have hdiv : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ∈ Nat.divisors 8 :=
    Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h | h | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h
  · exact (hne h).elim

/-- The central supplement transfers the fixed index from Z to its natural summand. -/
theorem edge_Z_index_eq_natural [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    (Z R b).relIndex (Z R a) = (Z R b).relIndex (U R a) := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hfixed : Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) ≤ Z R b := by
    rw [edge_Z_eq_fixed common a b ha hab]
    exact inf_le_inf_left _ (centralizer_le hQ)
  have hcover : U R a ⊔ Z R b = Z R a := by
    apply le_antisymm (sup_le (U_le_Z a) (edge_Z_le a b ha hab))
    conv_lhs => rw [naturalData.decomposition_at a ha]
    exact sup_le le_sup_left (hfixed.trans le_sup_right)
  let K := (Z R b).subgroupOf (Z R a)
  let A := (U R a).subgroupOf (Z R a)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (((edge_Z_le_Q common a b ha hab).trans (show Q R b ≤ stabilizer R b from
      fun _ hx => hx.1)).trans (Z_normalized R b))
  have hsup : A ⊔ K = ⊤ := by
    have hh := congrArg (fun H : Subgroup (FreeAmalgam R) => H.subgroupOf (Z R a)) hcover
    simpa only [subgroupOf_sup (U_le_Z a) (edge_Z_le a b ha hab), subgroupOf_self] using hh
  have hh := relIndex_sup_right A K
  rw [hsup, relIndex_top_right, relIndex_subgroupOf (U_le_Z a)] at hh
  exact hh

/-- Order-four edge displacement is precisely the fixed plane of the natural group. -/
theorem edge_fixed_natural_eq_commutator [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    U R a ⊓ Z R b = ⁅Z R a, Q R b⁆ := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  let C := U R a ⊓ Z R b
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U R a from inf_le_left))
    (inclusion_injective _)
  have hKC : ⁅Z R a, Q R b⁆ ≤ C := le_inf (edge_commutator_le_natural common a b ha hab) hZ
  have hCge : 4 ≤ Nat.card C := hcard ▸ card_le_of_le hKC
  have hdvd : Nat.card C ∣ 8 := common.natural.card_at a ha ▸ card_dvd_of_le
    (show C ≤ U R a from inf_le_left)
  have hne : Nat.card C ≠ 8 := by
    intro h
    have heq : C = U R a := eq_of_le_of_card_ge inf_le_left
      (by rw [h, common.natural.card_at a ha])
    have hfix : U R a ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
      have hh : U R a ≤ Z R b := heq ▸ (show C ≤ Z R b from inf_le_right)
      rw [edge_Z_eq_fixed common a b ha hab] at hh
      exact hh.trans inf_le_right
    apply edge_commutator_ne_bot common a b ha hab
    rw [edge_commutator_eq_natural common a b ha hab]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  have hdiv : Nat.card C ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hCcard : Nat.card C = 4 := by omega
  exact (eq_of_le_of_card_ge hKC (by rw [hCcard, hcard])).symm

/-- The fixed plane has index two in the actual natural group. -/
theorem edge_natural_index_of_card [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Z R b).relIndex (U R a) = 2 := by
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  have hfix := edge_fixed_natural_eq_commutator common a b ha hab hZ hcard
  have hF : (Z R b).subgroupOf (U R a) = (⁅Z R a, Q R b⁆).subgroupOf (U R a) := by
    rw [← hfix]
    ext x
    simp only [mem_subgroupOf, mem_inf, x.property, true_and]
  have hFcard : Nat.card ((Z R b).subgroupOf (U R a)) = 4 := by
    rw [hF, Nat.card_congr (subgroupOfEquivOfLe
      (edge_commutator_le_natural common a b ha hab)).toEquiv, hcard]
  have hh := ((Z R b).subgroupOf (U R a)).card_mul_index
  rw [hFcard, common.natural.card_at a ha] at hh
  change 4 * (Z R b).relIndex (U R a) = 8 at hh
  omega

/-- The source Z-index follows from containment and displacement order four. -/
theorem edge_Z_index_of_card [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Z R b).relIndex (Z R a) = 2 := by
  rw [edge_Z_index_eq_natural common a b ha hab]
  exact edge_natural_index_of_card common a b ha hab hZ hcard

/-- The first (4.6.6) follows in the binary case by evaluating the genuine edge action. -/
theorem edge_Q_index_of_card [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hZ : ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4) :
    (Q R a).relIndex (Q R b) = 4 := by
  let := geometry.U_elementary (lt_trans (by decide : 0 < 2) common.large_distance) a ha
  have hQ : Q R b ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hab)
  have hfixed : U R a ⊓ centralizer (Q R b : Set (FreeAmalgam R)) = U R a ⊓ Z R b := by
    rw [edge_Z_eq_fixed common a b ha hab, ← inf_assoc, inf_eq_left.mpr (U_le_Z a)]
  have hi : (U R a ⊓ centralizer (Q R b : Set (FreeAmalgam R))).relIndex (U R a) = 2 := by
    rw [hfixed, inf_relIndex_left]
    exact edge_natural_index_of_card common a b ha hab hZ hcard
  have hc : ⁅U R a, Q R b⁆ ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
    rw [← edge_commutator_eq_natural common a b ha hab]
    rw [edge_Z_eq_fixed common a b ha hab] at hZ
    exact hZ.trans inf_le_right
  have hindex := actor_index_eq_displacement_card_of_fixed_index_two (U R a) (Q R b)
    (hQ.trans (U_normalized a)) hc hi
  rw [← edge_commutator_eq_natural common a b ha hab, hcard] at hindex
  have hkernel : (Q R a).subgroupOf (Q R b) =
      (centralizer (U R a : Set (FreeAmalgam R))).subgroupOf (Q R b) := by
    ext x
    change (x : FreeAmalgam R) ∈ Q R a ↔ (x : FreeAmalgam R) ∈ centralizer (U R a : Set (FreeAmalgam R))
    rw [← common.natural.centralizer a ha, mem_inf]
    exact and_iff_right (hQ x.property)
  change ((Q R a).subgroupOf (Q R b)).index = 4
  rw [hkernel]
  exact hindex

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
