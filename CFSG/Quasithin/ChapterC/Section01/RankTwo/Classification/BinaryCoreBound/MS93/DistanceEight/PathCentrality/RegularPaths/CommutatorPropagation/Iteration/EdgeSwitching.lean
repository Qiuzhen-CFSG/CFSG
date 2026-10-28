module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Recurrence

/-!
# The natural-plane calculation for the backward edge in MS93 (4.4.4)

The terminal seed forces the failed-span commutator to have order four:
it properly contains the nonzero critical commutator. Two distinct planes
in the natural group of order eight generate that group. Consequently a
subgroup escaping the natural-action kernel cannot centralize two different
planes. Neighbor transitivity transfers the order to the backward edge.

This gives the exact backward-switching contract and its recurrence consumer
conditional on pointwise fixation of the backward edge by its own kernel.
That centrality premise is stronger than the source edge equality and is
not established here. The InvariantRadius extension gives a separate
conditional route through invariance of the radius image in the local quotient.
In particular, no edge-order or quadratic-action assertion from the older
contrary-configuration interfaces is assumed implicitly here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the radius-group step in (4.4.4), printed p.894. The radius group
is centered at the original starting vertex a.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The seed determines the order; no edge-order hypothesis is needed. -/
theorem seed_card_four (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K) :
    Nat.card K = 4 := by
  have hb := common.large_distance
  have hl := p.length_eq_b
  have ht : Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
    rw [show p.walk.length - 1 + 1 = p.walk.length by omega,
      SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have hKU : K ≤ U R a' := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural hb (moduleFacts common)
      a' _ p.end_color ht
  have hcard : Nat.card K ≤ 4 := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_displacement_card_le_four hb (moduleFacts common)
      a' _ p.end_color ht
  have hZQ : Z R a ≤ Q R (p.walk.getVert (p.walk.length - 1)) := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a p.start_color)
    rw [geometry.distance_constant a p.start_color, p.dist_start (by omega)]
    change p.walk.length - 1 < geometry.b R
    omega
  let C := ⁅Z R a, Z R a'⁆
  have hCK : C ≤ K := by
    rw [seed.terminal_edge, edgeCommutator, commutator_comm]
    exact commutator_mono hZQ le_rfl
  let : Finite (U R a') := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a' p.end_color]; decide)
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hCK) (inclusion_injective _)
  have hCZ : C ≤ Z R a := le_normalizer_iff_commutator_le_left.mp
    ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a))
  have hpos : 1 < Nat.card C := (one_lt_card_iff_ne_bot C).mpr
    (common.critical_noncommutation a p.start_color a' p.critical)
  have hlt : Nat.card C < Nat.card K := by
    by_contra! hh
    exact seed.not_le_start_Z ((eq_of_le_of_card_ge hCK hh).symm ▸ hCZ)
  obtain ⟨k, hk⟩ := card_dvd_of_le hCK
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  nlinarith

/-- Faithfulness rules out two different planes fixed by an escaping actor. -/
theorem planes_eq_of_fixed (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    {K E A : Subgroup (FreeAmalgam R)}
    (hK : K ≤ U R c) (hE : E ≤ U R c)
    (hKcard : Nat.card K = 4) (hEcard : Nat.card E = 4)
    (hA : A ≤ stabilizer R c) (hescape : ¬ A ≤ Q R c)
    (hKA : K ≤ centralizer (A : Set (FreeAmalgam R)))
    (hEA : E ≤ centralizer (A : Set (FreeAmalgam R))) : K = E := by
  let : Finite (U R c) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at c hc]; decide)
  let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
  let F := K ⊔ E
  have hFU : F ≤ U R c := sup_le hK hE
  let : Finite F := Finite.of_injective (inclusion hFU) (inclusion_injective _)
  by_contra hne
  have hEF : E < F := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hne (eq_of_le_of_card_ge (he ▸ (show K ≤ F from le_sup_left)) (by omega)))
  have hFlarge : 4 < Nat.card F := by
    rw [← hEcard]
    by_contra! h
    exact hEF.ne (eq_of_le_of_card_ge hEF.le h)
  have hFdiv : Nat.card F ∣ 8 := common.natural.card_at c hc ▸ card_dvd_of_le hFU
  have hdiv := Nat.mem_divisors.mpr ⟨hFdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hfull : F = U R c := eq_of_le_of_card_ge hFU
    (by rw [common.natural.card_at c hc]; omega)
  apply hescape
  rw [← common.natural.centralizer c hc]
  apply le_inf hA
  apply le_centralizer_iff.mp
  rw [← hfull]
  exact sup_le hKA hEA

/-- The backward edge is identified once its kernel fixes that edge pointwise. -/
theorem edge_switch_of_centrality (common : CommonFacts R source geometry)
    {c s t : Vertex R} (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K A : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4)
    (hA : A ≤ Q R s) (hescape : ¬ A ≤ Q R c)
    (hcomm : ⁅K, A⁆ = ⊥)
    (hcentral : edgeCommutator R c s ≤ centralizer (Q R s : Set (FreeAmalgam R))) :
    K = edgeCommutator R c s := by
  have hKU : K ≤ U R c := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) c t hc ht
  have hEU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) c s hc hs
  obtain ⟨g, _, hg⟩ := exists_edge_conjugator ht hs
  have hEcard : Nat.card (edgeCommutator R c s) = 4 := by
    rw [← hg, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, ← hforward]
    exact hcard
  exact planes_eq_of_fixed common hc hKU hEU hcard hEcard
    (hA.trans (fun _ hx => hx.2 c (adjacent_symm R hs))) hescape
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    (hcentral.trans (centralizer_le hA))

/-- A stronger local input for the centrality route, not an asserted source fact.
The forward edge and fixed-core premises are available at each induction stage. -/
def BackwardEdgeCentrality {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (K : Subgroup (FreeAmalgam R)) : Prop :=
  ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
      K = edgeCommutator R
        (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n + 1)) →
      K ≤ fixedCore R
        (p.walk.getVert (p.walk.length - 4 * n + 2)) →
      edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
        centralizer (Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) :
          Set (FreeAmalgam R))

/-- Radius escape and the plane calculation supply the literal switching contract,
with the actual failed-span commutator retained throughout. -/
theorem backwardEdgeSwitching_of_centrality (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hcentral : BackwardEdgeCentrality p (failedSpanCommutator p g)) :
    BackwardEdgeSwitching p (failedSpanCommutator p g) := by
  intro n hn hlen hforward hfixed
  have heven : Even (p.walk.length - 4 * n) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [← p.length_eq_b, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  obtain ⟨hcomm, hescape, hA⟩ := switching_ball_facts common p hg heven
    (by omega) (by omega)
  have hs : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n - 1)) := by
    apply adjacent_symm R
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 4 * n - 1) (by omega)
    rw [show p.walk.length - 4 * n - 1 + 1 = p.walk.length - 4 * n by omega] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have ht : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  exact edge_switch_of_centrality common ((p.vertex_color (by omega)).mpr heven)
    hs ht hforward (seed_card_four common p seed) hA hescape hcomm
    (hcentral n hn hlen hforward hfixed)


/-- Apply the proved local calculation to the existing source recurrence.
The centrality premise remains explicit; the source owner may instead prove
backward switching directly or use another sufficient local calculation. -/
theorem source_recurrence_of_centrality (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hcentral : BackwardEdgeCentrality p (failedSpanCommutator p g))
    (n : ℕ) (hn : 0 < n) (hbound : 4 * n < geometry.b R - 2) :
    failedSpanCommutator p g = edgeCommutator R
        (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n + 1)) ∧
      failedSpanCommutator p g ≤ fixedCore R
        (p.walk.getVert (p.walk.length - 4 * n - 2)) :=
  source_recurrence source p hp seed
    (backwardEdgeSwitching_of_centrality common p hg seed hcentral) n hn hbound


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching
