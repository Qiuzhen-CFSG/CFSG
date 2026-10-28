module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs

/-!
# Cubic local action and its two-core kernel

At a vertex of the genuine Section Seven coset graph whose stabilizer modulo
its two-core is `SL₂(2)`, the neighborhood has three vertices. Its pointwise
kernel is exactly that two-core, every incident edge stabilizer has order twice
the core order, and any subgroup of an edge stabilizer outside the core acts
transitively on the other two neighbors. These facts supply the local actions
needed in the four-path argument without any critical-path or order-eight
hypothesis.

The edge data of (7.3) put the core and a vertex Sylow 2-subgroup inside every
incident edge stabilizer. That edge stabilizer is proper: otherwise the edge
generation assertion would make the opposite stabilizer the whole group,
contradicting its nontrivial core and the trivial ambient core. Its image in
the six-element quotient therefore has index three. Local transitivity from
(7.1) and orbit-stabilizer give degree three, while counting gives the edge
order. The local kernel is normal and lies in this 2-group edge stabilizer,
so it lies in the two-core; (7.3) gives the reverse containment. Finally a
nonidentity permutation of three points fixing one interchanges the others.
The shared public neighbor action, core-edge containment, proper-edge and
stabilizer formulas are also used by the degree-five local calculation.
The auxiliary left action uses inverses to respect the graph's right action.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.54 / PDF p.44,
the paragraph beginning “Note that |Δ(δ)| = 3”, in
`refs/files/stellmacher-n-group.pdf`. Only genuine Sylow 2-data are used;
the questionable printed `Syl₃` assertion is not assumed.
-/

open scoped Pointwise

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u v

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
  (Γ : CosetGraphContext G S P1 P2)

private theorem mem_stabilizer {actor : G} {d : Γ.Vertex} :
    actor ∈ GAt Γ d ↔ Γ.act actor d = d := by
  exact Set.ext_iff.mp (Γ.stabilizer_def d) actor

private theorem exists_neighbor (d : Γ.Vertex) : ∃ t, Γ.adjacent d t := by
  obtain ⟨actor, hd | hd⟩ := Γ.coset₁_surjective d
  all_goals
    have hedge : Γ.adjacent (Γ.coset₁ actor) (Γ.coset₂ actor) := by
      rw [Γ.adj_cosets]
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨actor, Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
        Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  · exact ⟨Γ.coset₂ actor, hd ▸ hedge⟩
  · exact ⟨Γ.coset₁ actor, hd ▸ Γ.adjacent_symm hedge⟩

public theorem coset_neighbor_core_le_edge (h7 : SectionSevenHypotheses G S P1 P2)
    {d t : Γ.Vertex} (ht : Γ.adjacent d t) :
    QAt Γ d ≤ GAt Γ d ⊓ GAt Γ t := by
  refine le_inf ?_ ?_
  · change Γ.twoCoreAt d ≤ Γ.vertexStabilizer d
    rw [Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  · exact ((lemma_seven_three h7 Γ).sylow_and_core d t
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr ht) default).2.2

public theorem coset_neighbor_edge_proper (h7 : SectionSevenHypotheses G S P1 P2)
    {d t : Γ.Vertex} (ht : Γ.adjacent d t) :
    (GAt Γ d ⊓ GAt Γ t).subgroupOf (GAt Γ d) ≠ ⊤ := by
  have hdata := edge_sectionThree_data h7 Γ
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr ht) default
  intro heq
  have hle : GAt Γ d ≤ GAt Γ t := by
    intro actor hactor
    have : (⟨actor, hactor⟩ : GAt Γ d) ∈
        (GAt Γ d ⊓ GAt Γ t).subgroupOf (GAt Γ d) := by rw [heq]; trivial
    exact this.2
  have htop : GAt Γ t = ⊤ := by
    simpa only [sup_eq_right.mpr hle] using hdata.2.2.2.2.1
  have hne : twoCoreIn (GAt Γ t) ≠ ⊥ := hdata.2.2.1.1.2.2.1
  apply hne
  rw [htop]
  change (pCore 2 (⊤ : Subgroup G)).map
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom = ⊥
  rw [pCore_map_iso, h7.twoCore_eq_bot]

private theorem edge_index_three (h7 : SectionSevenHypotheses G S P1 P2)
    {d t : Γ.Vertex} (ht : Γ.adjacent d t)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two) :
    ((GAt Γ d ⊓ GAt Γ t).subgroupOf (GAt Γ d)).index = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  let edge := (GAt Γ d ⊓ GAt Γ t).subgroupOf (GAt Γ d)
  have hkerle : projection.ker ≤ edge := by
    rw [hker]
    exact Subgroup.subgroupOf_mono _ (coset_neighbor_core_le_edge Γ h7 ht)
  have hidx : (edge.map projection).index = edge.index :=
    edge.index_map_eq hsurj hkerle
  have hdvd : edge.index ∣ 6 := by
    rw [← hidx, ← SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    exact (edge.map projection).index_dvd_card
  obtain ⟨_, sylow, hsylow⟩ := ((lemma_seven_three h7 Γ).sylow_and_core d t
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr ht) default).1
  have hsle : (sylow : Subgroup (GAt Γ d)) ≤ edge := by
    intro actor hactor
    have hamb : (actor : G) ∈ sylowTwoAmbient (GAt Γ d ⊓ GAt Γ t) default := by
      rw [← hsylow]
      exact Subgroup.mem_map_of_mem _ hactor
    change (actor : G) ∈ GAt Γ d ⊓ GAt Γ t
    obtain ⟨edgeActor, _, heq⟩ := hamb
    exact heq ▸ edgeActor.property
  have hodd : ¬ 2 ∣ edge.index := fun hdiv =>
    sylow.not_dvd_index (hdiv.trans (Subgroup.index_dvd_of_le hsle))
  have hone : edge.index ≠ 1 := fun heq =>
    coset_neighbor_edge_proper Γ h7 ht (edge.index_eq_one.mp heq)
  have hbound := Nat.le_of_dvd (by decide : 0 < 6) hdvd
  change edge.index = 3
  interval_cases edge.index <;> omega

@[expose, instance_reducible] public def coset_neighbor_action (d : Γ.Vertex) :
    MulAction (GAt Γ d) {neighbor // Γ.adjacent d neighbor} where
  smul actor neighbor := ⟨Γ.act (actor : G)⁻¹ neighbor, by
    have hadj := adjacent_act Γ (actor : G)⁻¹ neighbor.property
    rwa [(mem_stabilizer Γ).mp ((GAt Γ d).inv_mem actor.property)] at hadj⟩
  one_smul neighbor := by
    apply Subtype.ext
    change Γ.act (1 : G)⁻¹ neighbor = neighbor
    simp only [inv_one, Γ.act_one]
  mul_smul first second neighbor := by
    apply Subtype.ext
    change Γ.act ((first : G) * (second : G))⁻¹ neighbor =
      Γ.act (first : G)⁻¹ (Γ.act (second : G)⁻¹ neighbor)
    rw [mul_inv_rev, Γ.act_mul]

public theorem coset_neighbor_stabilizer (d : Γ.Vertex)
    (neighbor : {neighbor // Γ.adjacent d neighbor}) :
    letI := coset_neighbor_action Γ d
    MulAction.stabilizer (GAt Γ d) neighbor =
      (GAt Γ d ⊓ GAt Γ neighbor).subgroupOf (GAt Γ d) := by
  let := coset_neighbor_action Γ d
  ext actor
  change (actor • neighbor = neighbor) ↔ _
  have hfix : actor • neighbor = neighbor ↔ Γ.act (actor : G)⁻¹ neighbor = neighbor :=
    Subtype.ext_iff
  rw [hfix, ← mem_stabilizer Γ]
  change ((actor : G)⁻¹ ∈ GAt Γ neighbor) ↔
    ((actor : G) ∈ GAt Γ d ∧ (actor : G) ∈ GAt Γ neighbor)
  simp only [Subgroup.inv_mem_iff, actor.property, true_and]

public theorem coset_neighbor_action_pretransitive
    (h7 : SectionSevenHypotheses G S P1 P2) (d : Γ.Vertex) :
    letI := coset_neighbor_action Γ d
    MulAction.IsPretransitive (GAt Γ d) {neighbor // Γ.adjacent d neighbor} := by
  let := coset_neighbor_action Γ d
  exact {
    exists_smul_eq := by
      intro first second
      obtain ⟨actor, hactor⟩ := (lemma_seven_one h7 Γ).local_transitivity d
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr first.property)
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr second.property)
      refine ⟨actor⁻¹, Subtype.ext ?_⟩
      change Γ.act ((actor : G)⁻¹)⁻¹ first = second
      simpa only [inv_inv] using hactor }

private theorem degree_three (h7 : SectionSevenHypotheses G S P1 P2)
    (d : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two) :
    Nat.card {neighbor // Γ.adjacent d neighbor} = 3 := by
  let := coset_neighbor_action Γ d
  let := coset_neighbor_action_pretransitive Γ h7 d
  obtain ⟨neighbor, hadj⟩ := exists_neighbor Γ d
  rw [← MulAction.index_stabilizer_of_transitive (GAt Γ d) ⟨neighbor, hadj⟩,
    coset_neighbor_stabilizer]
  exact edge_index_three Γ h7 hadj hmodel

private theorem edge_card_two (h7 : SectionSevenHypotheses G S P1 P2)
    {d t : Γ.Vertex} (ht : Γ.adjacent d t)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two) :
    QuotientCardEq (GAt Γ d ⊓ GAt Γ t) (QAt Γ d) 2 := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hindex := edge_index_three Γ h7 ht ⟨projection, hsurj, hker⟩
  have hgroup := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((coset_neighbor_core_le_edge Γ h7 ht).trans inf_le_left)).toEquiv,
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hgroup
  have hedge := ((GAt Γ d ⊓ GAt Γ t).subgroupOf (GAt Γ d)).index_mul_card
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show GAt Γ d ⊓ GAt Γ t ≤ GAt Γ d from inf_le_left)).toEquiv] at hedge
  unfold QuotientCardEq
  omega

public theorem coset_neighbor_kernel_of_edge_two_group
    (h7 : SectionSevenHypotheses G S P1 P2)
    {d neighbor : Γ.Vertex} (hadj : Γ.adjacent d neighbor)
    (hedgep : IsPGroup 2 ↥(GAt Γ d ⊓ GAt Γ neighbor))
    (actor : GAt Γ d) :
    (actor : G) ∈ QAt Γ d ↔
      ∀ other, Γ.adjacent d other → Γ.act (actor : G) other = other := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := coset_neighbor_action Γ d
  let representation := MulAction.toPermHom (GAt Γ d) {other // Γ.adjacent d other}
  have hkerle : representation.ker ≤
      (GAt Γ d ⊓ GAt Γ neighbor).subgroupOf (GAt Γ d) := by
    rw [← coset_neighbor_stabilizer Γ d ⟨neighbor, hadj⟩]
    intro member hmember
    exact congrArg (fun permutation => permutation ⟨neighbor, hadj⟩)
      (show representation member = 1 from hmember)
  have hkerp : IsPGroup 2 representation.ker :=
    (hedgep.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show GAt Γ d ⊓ GAt Γ neighbor ≤ GAt Γ d from inf_le_left)).symm).to_le hkerle
  have hkerCore : representation.ker ≤ pCore 2 (GAt Γ d) :=
    le_sSup ⟨inferInstance, hkerp⟩
  constructor
  · intro hactor other hother
    exact (mem_stabilizer Γ).mp ((coset_neighbor_core_le_edge Γ h7 hother hactor).2)
  · intro hfix
    have hmem : actor⁻¹ ∈ representation.ker := by
      change representation (actor⁻¹) = 1
      ext other
      change Γ.act ((actor : G)⁻¹)⁻¹ other = other
      simpa only [inv_inv] using hfix other other.property
    have hinv := hkerCore hmem
    have hactor := (pCore 2 (GAt Γ d)).inv_mem hinv
    change (actor : G) ∈ Γ.twoCoreAt d
    rw [Γ.twoCoreAt_def]
    change (actor : G) ∈ (pCore 2 (GAt Γ d)).map (GAt Γ d).subtype
    exact Subgroup.mem_map_of_mem (GAt Γ d).subtype (by simpa only [inv_inv] using hactor)

private theorem local_kernel (h7 : SectionSevenHypotheses G S P1 P2)
    (d : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two)
    (actor : GAt Γ d) :
    (actor : G) ∈ QAt Γ d ↔
      ∀ neighbor, Γ.adjacent d neighbor → Γ.act (actor : G) neighbor = neighbor := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := coset_neighbor_action Γ d
  let representation := MulAction.toPermHom (GAt Γ d) {neighbor // Γ.adjacent d neighbor}
  obtain ⟨neighbor, hadj⟩ := exists_neighbor Γ d
  have hedgep : IsPGroup 2 ↥(GAt Γ d ⊓ GAt Γ neighbor) := by
    have hcorep : IsPGroup 2 (QAt Γ d) := by
      change IsPGroup 2 (Γ.twoCoreAt d)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt Γ d)).map (GAt Γ d).subtype
    obtain ⟨power, hpower⟩ := IsPGroup.iff_card.mp hcorep
    apply IsPGroup.of_card (n := power + 1)
    rw [show Nat.card ↥(GAt Γ d ⊓ GAt Γ neighbor) = 2 * Nat.card (QAt Γ d)
      from edge_card_two Γ h7 hadj hmodel, hpower, pow_succ, mul_comm]
  exact coset_neighbor_kernel_of_edge_two_group Γ h7 hadj hedgep actor

private theorem perm_three_moves {Points : Type v} [Finite Points]
    (hcard : Nat.card Points = 3) (permutation : Equiv.Perm Points)
    (hne : permutation ≠ 1) {fixed first second : Points}
    (hfixed : permutation fixed = fixed)
    (hfirst : first ≠ fixed) (hsecond : second ≠ fixed)
    (hdistinct : first ≠ second) : permutation first = second := by
  classical
  let := Fintype.ofFinite Points
  have hcover : ({fixed, first, second} : Finset Points) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hcard]
    simp [hfirst.symm, hsecond.symm, hdistinct]
  have hall (member : Points) : member = fixed ∨ member = first ∨ member = second := by
    have hmem : member ∈ ({fixed, first, second} : Finset Points) := by
      rw [hcover]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hall (permutation first) with htofixed | hfirstfixed | htosecond
  · exact (hfirst (permutation.injective (htofixed.trans hfixed.symm))).elim
  · have hsecondfixed : permutation second = second := by
      rcases hall (permutation second) with htofixed | htofirst | htosecond
      · exact (hsecond (permutation.injective (htofixed.trans hfixed.symm))).elim
      · exact (hdistinct (permutation.injective (htofirst.trans hfirstfixed.symm)).symm).elim
      · exact htosecond
    apply (hne ?_).elim
    ext member
    rcases hall member with rfl | rfl | rfl
    · exact hfixed
    · exact hfirstfixed
    · exact hsecondfixed
  · exact htosecond

private theorem punctured_transitivity
    (h7 : SectionSevenHypotheses G S P1 P2)
    {d t : Γ.Vertex} (ht : Γ.adjacent d t)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two)
    (K : Subgroup G) (hK : K ≤ GAt Γ d ⊓ GAt Γ t) (hnot : ¬ K ≤ QAt Γ d) :
    IsActionTransitiveOn Γ K (neighborhood Γ d \ {t}) := by
  classical
  let : Finite Γ.Vertex := Γ.finiteVertex
  intro first second hfirst hsecond
  by_cases heq : first = second
  · exact ⟨1, by simpa only [OneMemClass.coe_one, Γ.act_one] using heq⟩
  obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
  have hactorD := (hK hactor).1
  have hactorT := (mem_stabilizer Γ).mp (hK hactor).2
  let := coset_neighbor_action Γ d
  let permutation := MulAction.toPermHom (GAt Γ d)
    {neighbor // Γ.adjacent d neighbor} ⟨actor⁻¹, (GAt Γ d).inv_mem hactorD⟩
  have happly (neighbor : {neighbor // Γ.adjacent d neighbor}) :
      (permutation neighbor : Γ.Vertex) = Γ.act actor neighbor := by
    change Γ.act (actor⁻¹)⁻¹ neighbor = _
    rw [inv_inv]
  have hne : permutation ≠ 1 := by
    intro heq
    apply houtside
    apply (local_kernel Γ h7 d hmodel ⟨actor, hactorD⟩).mpr
    intro neighbor hneighbor
    have hfix := congrArg (fun perm => (perm ⟨neighbor, hneighbor⟩ : Γ.Vertex)) heq
    simpa only [happly, Equiv.Perm.one_apply] using hfix
  have hfirstAdj := (SevenSix.mem_neighborhood_iff_adjacent Γ).mp hfirst.1
  have hsecondAdj := (SevenSix.mem_neighborhood_iff_adjacent Γ).mp hsecond.1
  have hmove := perm_three_moves (degree_three Γ h7 d hmodel) permutation hne
    (fixed := ⟨t, ht⟩) (first := ⟨first, hfirstAdj⟩) (second := ⟨second, hsecondAdj⟩)
    (Subtype.ext (by simpa only [happly] using hactorT))
    (fun heq => hfirst.2 (congrArg Subtype.val heq))
    (fun heq => hsecond.2 (congrArg Subtype.val heq))
    (fun hsub => heq (congrArg Subtype.val hsub))
  refine ⟨⟨actor, hactor⟩, ?_⟩
  simpa only [happly] using congrArg Subtype.val hmove

public structure CubicLocalActionConclusion (d : Γ.Vertex) : Prop where
  degree : Nat.card {neighbor // Γ.adjacent d neighbor} = 3
  kernel : ∀ actor : GAt Γ d, (actor : G) ∈ QAt Γ d ↔
    ∀ neighbor, Γ.adjacent d neighbor → Γ.act (actor : G) neighbor = neighbor
  edge_card : ∀ t, Γ.adjacent d t →
    QuotientCardEq (GAt Γ d ⊓ GAt Γ t) (QAt Γ d) 2
  punctured_transitivity : ∀ t, Γ.adjacent d t →
    ∀ K : Subgroup G, K ≤ GAt Γ d ⊓ GAt Γ t → ¬ K ≤ QAt Γ d →
      IsActionTransitiveOn Γ K (neighborhood Γ d \ {t})

public theorem cubic_local_action_of_sl2Two_quotient
    (h7 : SectionSevenHypotheses G S P1 P2) (d : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ d) (QAt Γ d) SL2Two) :
    CubicLocalActionConclusion Γ d where
  degree := degree_three Γ h7 d hmodel
  kernel := local_kernel Γ h7 d hmodel
  edge_card := fun _ ht => edge_card_two Γ h7 ht hmodel
  punctured_transitivity := fun _ ht => punctured_transitivity Γ h7 ht hmodel

end Stellmacher.SectionNine
