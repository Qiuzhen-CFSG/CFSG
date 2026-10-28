module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceFivePoint
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankFive
public import Theory.Representation.BinaryPermutation.FiveRankOneActors

/-!
# The normalized A₅ marked constituent and its actor

In the original small-actor branch, a faithful actor on a single A₅
constituent contradicts the rank-one module degree bound. At higher
multiplicity the orthogonal rank-one witness transfers to the selected
constituent through its trivial commutant. The five-point sign argument
then contradicts the original fixed line. Thus precisely two degree-four
copies remain: the whole degree is eight, the actor has rank three, and
its constituent kernel has order two.

The local-lift theorem retains the literal component, quotient marking,
and actor centralizer. Existing exchanged and A₆ source exclusions remove
those rows; L₂(8) remains a separate alternative. Ambient normalized A₅
recognition is still needed for terminal solvability.
Source: Aschbacher–Smith G.11.9, p.369, and 14.3.13–15, pp.993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private theorem five_parameters {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {A L : Subgroup D} {m : ℕ}
    (h : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ A L L m)
    (eL : L ≃* alternatingGroup (Fin 5)) :
    m ≤ 2 ∧ finrank (ZMod 2) V = 4 := by
  let e := eL.trans SL2FourNatural.alternatingFiveEquiv.symm
  have hc : Nat.card SL2FourNatural.F = 2^2 := by
    norm_num [Nat.card_eq_fintype_card, SL2FourNatural.card_field]
  obtain ⟨hm,hd⟩ := ChapterG.Section09.DefiningCharacteristic.rank_one_module_alternatives
    h e 2 (by decide) hc
  refine ⟨hm,?_⟩
  rcases hd with hd | ⟨n,hn,h2,hd,_⟩ | ⟨hbad,_⟩ <;> omega

namespace MarkedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

theorem not_actorFaithful_of_single_five
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    ¬ ActorFaithful (F := F) (g := g) (I := I) := by
  intro hf
  by_cases hi : I = ⊤
  · have h9 := s.componentHypothesis_of_whole hi
    rw [hHL] at h9
    obtain ⟨hm,hd⟩ := five_parameters h9 eL
    have h5 : 5 ∣ Nat.card F.TerminalHdot := by
      apply dvd_trans (b := Nat.card L) ?_ L.card_subgroup_dvd_card
      rw [Nat.card_congr eL.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
      s.many_overgroups s.seed_card s.centralizer_quotient.some
    have hr := Recognition.rankTwo_actor_rank_of_five_dvd h F
      (Recognition.rankTwo_closure_geometry h F s.nonabelian) s.nonabelian g
      s.parabolic_mem s.normalizer_not_mem s.hypothesis hd h5
    have ha := s.actor_dimension
    omega
  · have hsource := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
      s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
      s.centralizer_quotient.some F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected.isIrrPlus s.point_mem).2.2
    have hiso := hsource.2.resolve_right (fun h => hi h.1)
    have hisodim := B.twice_finrank_le_of_isotropic s.hypothesis.nondegenerate I hiso
    have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
    have h9 := s.componentHypothesis_of_actorFaithful hf
    dsimp only at h9
    rw [he] at h9
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    let a := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
      (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
    obtain ⟨hm,hd⟩ := five_parameters h9 (a.symm.trans eL)
    have ha := s.actor_dimension
    omega


open MarkedHigherTransport

/-- Transfer the actual rank-one orthogonal witness to the original marked
constituent using the trivial commutant of its natural A₅ action. -/
theorem source_higher_natural_five_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)))
    (x : F.terminalDot (F.X g))
    (hx : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp I.subtype)) = 1 := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨e,c,hc⟩ := hm
  obtain ⟨J,hJ,_,_,hxJ,hr⟩ := s.source_exists_orthogonal_constituent_rank_one hk hd x hx
  let R := invariantSubspace F.terminalRepresentation H J hJ.choose
  have hi : IsIrreducible R.toRepresentation :=
    hJ.irreducible_of_normal_restriction F.terminalRepresentation
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H
  obtain ⟨E,hE⟩ := s.constituents_sameModule R hi
  let X := zpowers (x : F.TerminalHdot)
  have hXI : X ≤ subspaceStabilizer F.terminalRepresentation I :=
    zpowers_le.mpr (s.actor_stabilizes x.property)
  have hXJ : X ≤ subspaceStabilizer F.terminalRepresentation J := zpowers_le.mpr hxJ
  let P := H ⊔ X
  have hHP : H ≤ P := le_sup_left
  let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H X I s.selected.invariant hXI
  let τ := ChapterG.Section09.constituentAction F.terminalRepresentation H X J hJ.choose hXJ
  have hEP : ∀ p : P, ∀ u, E (σ p u) = τ p (E u) := by
    apply Representation.marked_equivariant_of_trivial_normal_commutant σ τ (H.subgroupOf P) E
    · intro h u
      exact hE ⟨h.val.val,h.property⟩ u
    · intro f hf
      apply Representation.FivePointActors.natural_commuting_eq_refl
        (invariantSubspace F.terminalRepresentation H I s.selected.invariant).toRepresentation
        e c hc f
      intro h u
      exact hf ⟨⟨h,hHP h.property⟩,h.property⟩ u
  let xp : P := ⟨x,(show X ≤ P from le_sup_right) (mem_zpowers _)⟩
  have ht := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv
    E (σ xp) (τ xp) (hEP xp)
  have hrI := constituent_displacement_rank F.terminalRepresentation H X I
    s.selected.invariant hXI ⟨x,mem_zpowers _⟩
  have hrJ := constituent_displacement_rank F.terminalRepresentation H X J
    hJ.choose hXJ ⟨x,mem_zpowers _⟩
  exact hrI.symm.trans (ht.trans (hrJ.trans hr))

/-- The natural A₅ higher-multiplicity row contradicts the actual marked
fixed line. Its orthogonal rank-one witnesses force at most two actions. -/
theorem not_higher_natural_five
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section09.Quasiequivalent
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5))) : False := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let : H.Normal := componentOrbit_top_normal L
  let P := H ⊔ X
  have hHP : H ≤ P := le_sup_left
  have hXP : X ≤ P := le_sup_right
  let σ := MarkedAction.action F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes
  let j : X →* X.subgroupOf P := {
    toFun := fun x => ⟨⟨x,hXP x.property⟩,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hfix (x : X) : σ (j x) = 1 ↔ (x : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot) := by
    rw [← source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.nonsolvable s.hypothesis
      s.component s.moved s.selected.isIrrPlus s.point_mem x]
    constructor
    · intro he u
      exact congrArg Subtype.val (LinearMap.congr_fun he u)
    · intro he
      ext u
      exact he u
  have hn : ¬ X ≤ centralizer (H : Set F.TerminalHdot) := by
    intro h
    exact (ne_of_lt s.actor_centralizer_lt) (inf_eq_left.mpr h)
  obtain ⟨a,ha,haC⟩ := SetLike.not_le_iff_exists.mp hn
  let aX : X := ⟨a,ha⟩
  have haσ : σ (j aX) ≠ 1 := fun he => haC ((hfix aX).mp he)
  obtain ⟨e,c,hc⟩ := hm
  let eH := (subgroupOfEquivOfLe hHP).trans e
  have hacts := Representation.FivePointActors.two_actions_of_rank_one σ (H.subgroupOf P) (X.subgroupOf P)
    eH c (fun h u => hc ⟨h.val.val,h.property⟩ u) ?_ (j aX) haσ
  · apply s.false_of_two_actor_actions (s.source_fixedSpace_eq_point_of_higher_dimension hd) aX
    · intro x
      rcases hacts (j x) with h | h
      · exact Or.inl (fun u => congrArg Subtype.val (h u))
      · exact Or.inr (fun u => congrArg Subtype.val (h u))
    · exact (s.source_higher_natural_five_rank_one hk hd ⟨e,c,hc⟩ aX haC).le
  · intro x hx
    let xX : X := ⟨x.val.val,x.property⟩
    have hxC : (xX : F.TerminalHdot) ∉ centralizer (H : Set F.TerminalHdot) :=
      fun h => hx ((hfix xX).mpr h)
    exact (constituent_displacement_rank F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes xX).trans
      (s.source_higher_natural_five_rank_one hk hd ⟨e,c,hc⟩ xX hxC)


/-- In the surviving normalized marked row the constituent has degree four,
while the whole module has at least two copies. -/
theorem single_five_constituent_four
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    finrank (ZMod 2) I = 4 ∧ 8 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
  have hk := s.not_actorFaithful_of_single_five hHL eL
  have hdim : finrank (ZMod 2) I = 4 := by
    rcases s.constituent_dimension_cases_of_not_actorFaithful hk with hd | hd
    · have h9 := s.singleOrbit_componentHypothesis_of_double_dimension hk hd hHL
      have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
      dsimp only at h9
      rw [he] at h9
      let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
      let a := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
        (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
      exact (five_parameters h9 (a.symm.trans eL)).2
    · obtain ⟨n,hn,hn8,a,c,hc⟩ := s.source_higher_natural_model hk hd
      have heq : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin 5)) :=
        (Nat.card_congr a.toEquiv).symm.trans
          (Nat.card_congr ((MulEquiv.subgroupCongr hHL).trans eL).toEquiv)
      have hn5 : n = 5 := by
        interval_cases n <;> try rfl
        all_goals
          rw [nat_card_alternatingGroup,nat_card_alternatingGroup] at heq
          norm_num [Nat.factorial] at heq
      subst n
      exact c.finrank_eq.trans (by
        rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
        decide)
  refine ⟨hdim,?_⟩
  have hh := s.twice_constituent_finrank_le_of_not_actorFaithful hk
  omega

/-- The normalized A₅ marked source has exactly two degree-four copies. -/
theorem single_five_degree_eight
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    finrank (ZMod 2) (Additive F.Uhat) = 8 := by
  have hk := s.not_actorFaithful_of_single_five hHL eL
  have hi := (s.single_five_constituent_four hHL eL).1
  rcases s.constituent_dimension_cases_of_not_actorFaithful hk with hd | hd
  · omega
  · obtain ⟨n,hn,hn8,a,c,hc⟩ := s.source_higher_natural_model hk hd
    have heq : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin 5)) :=
      (Nat.card_congr a.toEquiv).symm.trans
        (Nat.card_congr ((MulEquiv.subgroupCongr hHL).trans eL).toEquiv)
    have hn5 : n = 5 := by
      interval_cases n <;> try rfl
      all_goals
        rw [nat_card_alternatingGroup,nat_card_alternatingGroup] at heq
        norm_num [Nat.factorial] at heq
    subst n
    exact (s.not_higher_natural_five hk hd ⟨a,c,hc⟩).elim

/-- The original actor has rank three and its constituent kernel has order two. -/
theorem single_five_actor_parameters
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
    Nat.card ((centralizer (L : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))) = 2 := by
  have hd := s.single_five_degree_eight hHL eL
  have hi := (s.single_five_constituent_four hHL eL).1
  have ha := s.actor_dimension
  refine ⟨by omega,?_⟩
  have hh := s.actor_kernel_card_two_of_double_dimension
    (s.not_actorFaithful_of_single_five hHL eL) (by omega)
  simpa only [hHL] using hh

/-- The original marked source yields the same normalized lift with its
nonfaithful degree-four constituent and exact degree-eight actor data,
or the independently handled L₂(8) row. -/
theorem local_lift_single_five_actor_or_eight :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        F.terminalDot K = L ∧ Nonempty (L ≃* alternatingGroup (Fin 5)) ∧
        ¬ ActorFaithful (F := F) (g := g) (I := I) ∧
        finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nat.card ((centralizer (L : Set F.TerminalHdot)).subgroupOf
          (F.terminalDot (F.X g))) = 2) ∨
        EightImageRow F K) := by
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hnormal⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L s.component
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ s.component,he.symm ▸ s.moved,hnormal⟩
  have hcases := source_component_cases_of_small_actor s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor
    hK (he.symm ▸ s.recognized_componentImageCases)
  have hn : L.Normal := by
    by_contra hn
    have hi := s.whole_of_component_not_normal hn
    have hHL : componentOrbit L ⊤ ≠ L :=
      fun hh => hn (hh ▸ componentOrbit_top_normal L)
    exact source_exchanged_a5_false s.simple T s.empty s.maximal s.unique_overgroup
      s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis hK
      (s.actionModel_of_whole_pair_eight hi hHL
        (s.degree_eight_of_whole_pair hi hHL) hK he).some
  have hHL : componentOrbit L ⊤ = L := by
    let := hn
    exact le_antisymm
      (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top]))
      (le_componentOrbit L ⊤)
  have hspan := hK.eq_conjugateSpanBy_of_image_normal (he.symm ▸ hn)
  rcases source_component_cases_reduce s.simple T s.empty s.maximal s.unique_overgroup
      s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model
      F g K hK hcases with h5 | h8
  · rcases h5 with h5 | h6
    · let eL := (MulEquiv.subgroupCongr he).symm.trans h5.some
      exact ⟨K,hK,Or.inl ⟨hspan,he,⟨eL⟩,s.not_actorFaithful_of_single_five hHL eL,
        (s.single_five_constituent_four hHL eL).1, s.single_five_degree_eight hHL eL,
        s.single_five_actor_parameters hHL eL⟩⟩
    · exact (source_terminal_a6_false s.simple T s.empty s.maximal s.unique_overgroup
        s.many_overgroups s.seed_card s.centralizer_quotient.some s.not_model
        F s.nonabelian g s.parabolic_mem s.normalizer_not_mem hK h6.some).elim
  · exact ⟨K,hK,Or.inr h8⟩

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
