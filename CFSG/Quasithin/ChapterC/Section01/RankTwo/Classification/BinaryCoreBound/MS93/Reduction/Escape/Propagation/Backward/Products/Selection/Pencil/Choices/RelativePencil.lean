module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil

/-!
# Pencil comparisons for the source relative normalizer

MS93 defines G_(a,t) as N_(G_a)(Q_t), not as the edge stabilizer.
This relative normalizer normalizes [Z_a,Q_t]. If the critical line
lay in that displacement, the endpoint would normalize it as well;
generation would then make a plane invariant under the full natural
three-dimensional action, contradicting its full commutator.

The resulting noncontainment gives the order-two intersection and its
join with the critical line. These are conditional pencil comparisons;
the two actual generating choices are a separate local-model argument.
All legacy edge-stabilizer statements are retained in their original modules.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), notation on p.881 and (4.3.7)(i), p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
/-- The literal source relative normalizer preserves its displacement plane. -/
theorem relativeNormalizer_normalizes_edgeDisplacement (a t : Vertex R) :
    stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R)) ≤
      normalizer (edgeDisplacement a t : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Z R a, Q R t⁆).map (MulAut.conj g).toMonoidHom = _
  have hZ := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hg.1)
  have hQ := mem_normalizer_iff_map_conj_eq.mp hg.2
  change (Z R a).map (MulAut.conj g).toMonoidHom = Z R a at hZ
  change (Q R t).map (MulAut.conj g).toMonoidHom = Q R t at hQ
  rw [map_commutator, hZ, hQ]
  rfl

private theorem four_index_in_eight {G : Type*} [Group G]
    (A U : Subgroup G) (hAU : A ≤ U) (hA : Nat.card A = 4) (hU : Nat.card U = 8) :
    A.relIndex U = 2 := by
  have hh := (A.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv, hA, hU] at hh
  change 4 * A.relIndex U = 8 at hh
  omega

/-- The endpoint has order two in the actual quotient at the start.
This is the critical-index identity in the reverse direction, using
the supplied natural decomposition on both endpoints. -/
theorem endpoint_actor_index (source : LocalSource L R)
    (p : Counterexample geometry) (modules : ModuleFacts source geometry)
    (initial : InitialFacts p) : (Q R p.a).relIndex (Z R p.a') = 2 := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  rw [s.critical_Z_index_eq_U geometry p.a' p.end_color p.a
    (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical)]
  rw [← modules.critical_U_index p.a p.color_a p.a' p.critical,
    ← s.critical_Z_index_eq_U geometry p.a p.color_a p.a' p.critical]
  exact initial.critical_index

/-- A source generating relative normalizer has displacement missing the critical line. -/
theorem critical_not_le_generating_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' = stabilizer R p.a) :
    ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a t := by
  intro hR
  let A := edgeDisplacement p.a t
  have hAZ : A ≤ Z R p.a := (Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)
  have hAN : stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R)) ≤
      normalizer (A : Set (FreeAmalgam R)) :=
    relativeNormalizer_normalizes_edgeDisplacement p.a t
  have hEnd : Z R p.a' ≤ normalizer (A : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hAZ le_rfl).trans hR)
  have hlocal : stabilizer R p.a ≤ normalizer (A : Set (FreeAmalgam R)) :=
    hgen ▸ sup_le hAN hEnd
  have hAU : A ≤ U R p.a := Initial.edge_le_natural source p.a t p.color_a hat
  have hcard : Nat.card A = 4 := edge_card p (by omega) initial p.a t p.color_a hat
  have hsmall : ⁅U R p.a, stabilizer R p.a⁆ ≤ A :=
    commutator_le_of_normalized_index_two _ _ _ hAU
      (four_index_in_eight _ _ hAU hcard (modules.natural.card_at p.a p.color_a))
      (U_normalized p.a) hlocal
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hfull : ⁅U R p.a, stabilizer R p.a⁆ = U R p.a := by
    rw [commutator_comm, commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at p.a p.color_a).symm)
      inf_le_right ((U_le_Z p.a).trans ((Z_le_stabilizer R p.a).trans (stabilizer R p.a).le_normalizer)),
      commutator_comm]
    exact Initial.Z_commutator_stabilizer source p.a p.color_a
  rw [hfull] at hsmall
  have hh := congrArg (fun K : Subgroup (FreeAmalgam R) => Nat.card K) (le_antisymm hAU hsmall)
  rw [hcard, modules.natural.card_at p.a p.color_a] at hh
  omega

/-- A generating edge cuts the first plane in a line of order two. -/
theorem edgeLine_card_of_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' = stabilizer R p.a) :
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
    apply critical_not_le_generating_relativeNormalizer source p hb modules initial t hat hgen
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
theorem edgeLine_join_critical_of_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' = stabilizer R p.a) :
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
      (by rw [edgeLine_card_of_relativeNormalizer source p hb modules initial control edge β t hβ hat hgen]; exact hsmall)
    have hR : criticalCommutator p.a p.a' ≤ edgeLine p β t := hline.symm ▸ le_sup_right
    exact critical_not_le_generating_relativeNormalizer source p hb modules initial t hat hgen
      (hR.trans inf_le_left)
  have hdiv := Nat.mem_divisors.mpr ⟨hB ▸ card_dvd_of_le hAB, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hAc : Nat.card A = 4 := by omega
  exact eq_of_le_of_card_ge hAB (by rw [hB, hAc])


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
