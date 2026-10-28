module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Commutators

/-!
# The endpoint fixed plane and its intersection lines

Critical minimality puts Z_(a') in the first edge kernel. Its fixed group
on U_a contains the order-four edge plane and is proper by faithfulness
and critical reversal, so it is exactly that plane. A generating edge
cannot contain the critical commutator. The two order-four planes in U_a
therefore meet in a line of order two; adjoining the critical commutator
recovers the first plane.

Only the existence of two generating edges with different lines remains
for the local marked-model calculation. No assertion about W(t) is used
in these plane and line identifications.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The endpoint Z-layer is in the first edge kernel, by strict critical
minimality in the reversed direction. -/
theorem endpoint_le_first_kernel (p : Counterexample geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) : Z R p.a' ≤ Q R β := by
  apply Z_le_Q_of_dist_lt R p.a' (geometry.exists_critical p.a' p.end_color)
  rw [geometry.distance_constant p.a' p.end_color]
  change (cosetGraph R).dist p.a' β < geometry.b R
  have hpath := hβ.2
  rw [SimpleGraph.dist_comm (u := p.a') (v := p.a), p.distance_eq_b] at hpath
  omega

/-- The critical line lies in the displacement of the first path edge. -/
theorem critical_le_first_edge (p : Counterexample geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) :
    criticalCommutator p.a p.a' ≤ edgeDisplacement p.a β :=
  commutator_mono le_rfl (endpoint_le_first_kernel p β hβ)

/-- The genuine endpoint-fixed group on the natural eight is the first
edge plane. This uses faithfulness, rather than just matching cardinalities. -/
theorem endpoint_fixed_plane (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) :
    U R p.a ⊓ centralizer (Z R p.a' : Set (FreeAmalgam R)) =
      edgeDisplacement p.a β := by
  let C := U R p.a ⊓ centralizer (Z R p.a' : Set (FreeAmalgam R))
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at p.a p.color_a]; decide)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ U R p.a from inf_le_left)) (inclusion_injective _)
  have hE : edgeDisplacement p.a β ≤ C := by
    refine le_inf (Initial.edge_le_natural source p.a β p.color_a hβ.endpoint_adjacent) ?_
    have hZ := edge_le_Z p hb control edge p.a β p.color_a hβ.endpoint_adjacent
    rw [EdgeTransfer.edge_Z_eq_fixed hb modules p.a β p.color_a hβ.endpoint_adjacent] at hZ
    exact (hZ.trans inf_le_right).trans (centralizer_le (endpoint_le_first_kernel p β hβ))
  have hEcard := edge_card p (by omega) initial p.a β p.color_a hβ.endpoint_adjacent
  have hCge : 4 ≤ Nat.card C := hEcard ▸ card_le_of_le hE
  have hCdiv : Nat.card C ∣ 8 := modules.natural.card_at p.a p.color_a ▸
    card_dvd_of_le (show C ≤ U R p.a from inf_le_left)
  have hCne : Nat.card C ≠ 8 := by
    intro hc
    have heq : C = U R p.a := eq_of_le_of_card_ge inf_le_left
      (by rw [hc, modules.natural.card_at p.a p.color_a])
    have hfix : U R p.a ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) :=
      heq ▸ (show C ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) from inf_le_right)
    apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    rw [← modules.natural.centralizer p.a p.color_a]
    exact le_inf p.end_Z_le_start_stabilizer (le_centralizer_iff.mp hfix)
  have hdiv := Nat.mem_divisors.mpr ⟨hCdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  exact (eq_of_le_of_card_ge hE (by rw [hEcard]; omega)).symm

/-- The line can equally be computed as the intersection of the two
actual edge displacements. -/
theorem edgeLine_eq_inf_displacements (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t) :
    edgeLine p β t = edgeDisplacement p.a t ⊓ edgeDisplacement p.a β := by
  have hfixed := edge_fixed_natural_eq_commutator hb modules p.a β p.color_a hβ.endpoint_adjacent
    (edge_le_Z p hb control edge p.a β p.color_a hβ.endpoint_adjacent)
    (edge_card p (by omega) initial p.a β p.color_a hβ.endpoint_adjacent)
  change U R p.a ⊓ Z R β = edgeDisplacement p.a β at hfixed
  rw [← hfixed, ← inf_assoc,
    inf_eq_left.mpr (Initial.edge_le_natural source p.a t p.color_a hat)]
  rfl

/-- A generating edge cuts the first plane in a line of order two. -/
theorem edgeLine_card (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
    Nat.card (edgeLine p β t) = 2 := by
  let A := edgeDisplacement p.a t
  let B := edgeDisplacement p.a β
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at p.a p.color_a]; decide)
  have hAU : A ≤ U R p.a := Initial.edge_le_natural source p.a t p.color_a hat
  have hBU : B ≤ U R p.a := Initial.edge_le_natural source p.a β p.color_a hβ.endpoint_adjacent
  let : Finite A := Finite.of_injective (inclusion hAU) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion hBU) (inclusion_injective _)
  have hA : Nat.card A = 4 := edge_card p (by omega) initial p.a t p.color_a hat
  have hB : Nat.card B = 4 := edge_card p (by omega) initial p.a β p.color_a hβ.endpoint_adjacent
  have hindex : B.relIndex (U R p.a) = 2 := by
    have hh := (B.subgroupOf (U R p.a)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBU).toEquiv, hB,
      modules.natural.card_at p.a p.color_a] at hh
    change 4 * B.relIndex (U R p.a) = 8 at hh
    omega
  have hsmall : B.relIndex A ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := B) hAU (by rw [hindex]; decide)
    rwa [hindex] at hh
  have hnotle : ¬ A ≤ B := by
    intro hAB
    have heq : A = B := eq_of_le_of_card_ge hAB (by rw [hA, hB])
    apply critical_not_le_generating_edge source p hb modules initial t hat hgen
    change criticalCommutator p.a p.a' ≤ A
    rw [heq]
    exact critical_le_first_edge p β hβ
  have hne : B.relIndex A ≠ 1 := fun h => hnotle (relIndex_eq_one.mp h)
  have hcard := ((A ⊓ B).subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ A from inf_le_left)).toEquiv,
    hA] at hcard
  change Nat.card (A ⊓ B : Subgroup (FreeAmalgam R)) * (A ⊓ B).relIndex A = 4 at hcard
  rw [inf_relIndex_left] at hcard
  have hnonzero : B.relIndex A ≠ 0 := by intro h; rw [h, mul_zero] at hcard; omega
  have htwo : B.relIndex A = 2 := by omega
  rw [htwo] at hcard
  rw [edgeLine_eq_inf_displacements source p hb modules initial control edge β t hβ hat]
  change Nat.card (A ⊓ B : Subgroup (FreeAmalgam R)) = 2
  omega

/-- The line and the critical commutator generate the first edge plane. -/
theorem edgeLine_join_critical (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
    edgeLine p β t ⊔ criticalCommutator p.a p.a' = edgeDisplacement p.a β := by
  let A := edgeLine p β t ⊔ criticalCommutator p.a p.a'
  let B := edgeDisplacement p.a β
  have hB : Nat.card B = 4 := edge_card p (by omega) initial p.a β p.color_a hβ.endpoint_adjacent
  let : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; decide)
  have hAB : A ≤ B := by
    apply sup_le _ (critical_le_first_edge p β hβ)
    rw [edgeLine_eq_inf_displacements source p hb modules initial control edge β t hβ hat]
    exact inf_le_right
  let : Finite A := Finite.of_injective (inclusion hAB) (inclusion_injective _)
  have hlarge : 2 < Nat.card A := by
    by_contra! hsmall
    have hline : edgeLine p β t = A := eq_of_le_of_card_ge le_sup_left
      (by rw [edgeLine_card source p hb modules initial control edge β t hβ hat hgen]; exact hsmall)
    have hR : criticalCommutator p.a p.a' ≤ edgeLine p β t := hline.symm ▸ le_sup_right
    exact critical_not_le_generating_edge source p hb modules initial t hat hgen
      (hR.trans inf_le_left)
  have hdiv := Nat.mem_divisors.mpr ⟨hB ▸ card_dvd_of_le hAB, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hAc : Nat.card A = 4 := by omega
  exact eq_of_le_of_card_ge hAB (by rw [hB, hAc])

/-- All pencil identities are now proved; the remaining local geometric
input is the existence of two generating edges with distinct lines. -/
theorem pencilFacts_of_two_lines (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1)
    (htwo : ∃ t u, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
      Adjacent R p.a u ∧
      (stabilizer R p.a ⊓ stabilizer R u) ⊔ Z R p.a' = stabilizer R p.a ∧
      edgeLine p β t ≠ edgeLine p β u) : PencilFacts p β where
  fixed_plane := endpoint_fixed_plane source p hb modules initial control edge β hβ
  line_card := fun t ht hgen => edgeLine_card source p hb modules initial control edge β t hβ ht hgen
  line_join := fun t ht hgen => edgeLine_join_critical source p hb modules initial control edge β t hβ ht hgen
  two_lines := htwo

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
