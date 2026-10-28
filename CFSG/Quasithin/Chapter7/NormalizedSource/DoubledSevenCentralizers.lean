module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceSelection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The cyclic obstruction in the doubled A₇ row

The original E.6.7 block and E.6.8 component theorems construct the regular
cyclic subgroup at every maximal member of the actual obstruction family Γ.
Its faithful action supplies an element of order 2ⁿ − 1 in the literal
image of C_M(U) on W. If n is four or five, a faithful seven-letter action
rules this out: a permutation on seven letters has neither order 15 nor 31.
The order-15 exclusion uses the disjoint cycle lengths, not a group-order
argument (15 does divide |S₇|).

These are the terminal cyclic-action steps in 7.5.5. Membership in Γ is
retained as the original O^{2′} condition; it is not replaced by a desired
numerical bound or by the existence of a merely moving element.
Source: Aschbacher–Smith E.6.11(2), pp.249–250, and 7.5.5, p.701.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterE.Section06 ChapterE.Section06.FrobeniusReduction
open ChapterE.Section06.Components ChapterE.Section06.InvariantSubspaces.BlockSelection

/-- Cycle lengths three and five cannot fit disjointly on seven letters. -/
theorem doubledSeven_no_fifteen (g : Equiv.Perm (Fin 7)) : orderOf g ≠ 15 := by
  intro hg
  have hmem {n : ℕ} (hn : n ∈ g.cycleType) : n = 3 ∨ n = 5 := by
    have hd := g.dvd_of_mem_cycleType hn
    rw [hg] at hd
    have hlo := g.two_le_of_mem_cycleType hn
    have hhi := (Multiset.le_sum_of_mem hn).trans g.sum_cycleType_le
    simp only [Fintype.card_fin] at hhi
    interval_cases n <;> norm_num at *
  have h3 : 3 ∈ g.cycleType := by
    by_contra hn
    have hc : g.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr (by
      intro n hn'
      rcases hmem hn' with rfl | rfl
      · exact (hn hn').elim
      · exact dvd_rfl)
    rw [g.lcm_cycleType,hg] at hc
    norm_num at hc
  have h5 : 5 ∈ g.cycleType := by
    by_contra hn
    have hc : g.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr (by
      intro n hn'
      rcases hmem hn' with rfl | rfl
      · exact dvd_rfl
      · exact (hn hn').elim)
    rw [g.lcm_cycleType,hg] at hc
    norm_num at hc
  have h5' : 5 ∈ g.cycleType.erase 3 :=
    (Multiset.mem_erase_of_ne (by decide : 5 ≠ 3)).mpr h5
  have hlo := Multiset.le_sum_of_mem h5'
  have hsum := g.sum_cycleType_le
  rw [← Multiset.cons_erase h3,Multiset.sum_cons] at hsum
  simp only [Fintype.card_fin] at hsum
  omega

/-- An order-31 element is excluded by the order of S₇. -/
theorem doubledSeven_no_thirtyOne (g : Equiv.Perm (Fin 7)) : orderOf g ≠ 31 := by
  intro hg
  have hd := orderOf_dvd_natCard g
  rw [hg] at hd
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hd

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M W U : Subgroup G}

private theorem maximal_regular_section
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hU : U ∈ obstructionFamily M W)
    (hmax : ∀ Y : Subgroup G, U < Y → Y ≤ W → centralizer (Y : Set G) ≤ M)
    (hn : 1 < subgroupCorank W U) :
    ∃ X : Subgroup G, RegularCyclicSection M W U X := by
  let _ := h.elementary
  have ho := h.oddCore_eq_bot_of_maximal_escape (source_earlierLocalFacts h) hU hmax hn
  have hfixed {L : Subgroup G} (hLH : L ≤ centralizer (U : Set G)) (hLM : ¬ L ≤ M) :
      W ⊓ centralizer (L : Set G) = U :=
    (fixedSpace_eq_of_maximal_escape hU.1 hmax hLH hLM).symm
  rcases component_or_characteristicTwo_of_maximal_escape h hU hmax hn with
    ⟨L,hL⟩ | hc
  · have hf := hfixed hL.1 (component_not_le h (source_earlierLocalFacts h) hU hL)
    have hcor : actionCorank W L = subgroupCorank W U := by rw [actionCorank,hf]
    rcases RemainingSieve.adequateComponentAlternatives_knownSimple h hU hL with
      ⟨n,hb⟩ | ⟨n,hs⟩ | hfour | ha | hodd
    · obtain ⟨s⟩ := minimalRegularSection_of_borel h ho hU hL hf hn hb
      exact ⟨s.torus,s.regular⟩
    · obtain ⟨s⟩ := minimalRegularSection_of_symplectic h ho hU hL hf hmax hn hs
      exact ⟨s.torus,s.regular⟩
    · have he := hfour.2.2.1
      rw [hcor] at he
      omega
    · obtain ⟨A,hUA,hAW,he,heA⟩ := ha.escape
      have hlt : U < A := lt_of_le_of_ne hUA (by
        intro heq
        rw [← heq] at he
        omega)
      exact (heA (inf_le_right.trans (hmax A hlt hAW))).elim
    · have he := hodd.2.1
      rw [hcor] at he
      omega
  · obtain ⟨d⟩ := e67Input_knownSimple h U hU (centralizer (U : Set G))
      (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc
    have hex : ∃ i, ¬ d.block i ≤ M := by
      by_contra! hall
      exact hU.2.2.1 (d.generated.le.trans (sup_le inf_le_right (iSup_le hall)))
    obtain ⟨i,hi⟩ := hex
    have hf := hfixed (d.le i) hi
    have ha (n : ℕ) : ¬ ChapterC.IsAlternatingBlock (d.block i) n := by
      intro ht
      have he := (d.alternating i n ht).1
      rw [hf] at he
      omega
    obtain ⟨n,ht⟩ : ∃ n, ChapterC.IsL2EvenBlock (d.block i) n := by
      rcases d.type i with ht | ht | ht
      · exact ht
      · exact (ha 3 ht).elim
      · exact (ha 5 ht).elim
    have hb : Hyperplanes.Enlargement.BlockInspection.CentralizerBlock U (d.block i) :=
      ⟨d.le i,inferInstance,ht.2.1.of_mulEquiv (subgroupOfEquivOfLe (d.le i)).symm,
        d.subnormal i⟩
    obtain ⟨_,_,_,_,_,_,_,_,hB,_⟩ := d.rankOne i n ht
    obtain ⟨hWL,X,hXP,hcyc,hcard,hgen,hdis,hWcard,hprod,_,_,hreg⟩ :=
      source_rankOne_of_borel h hU
        (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc (d.le i) hb.2 hi ht hB
    have hXW : ⁅W,X⁆ ≤ W := le_sup_right.trans hgen.symm.le
    have hXN : ⁅W,X⁆ ≤ normalizer (W ⊓ centralizer (d.block i : Set G) : Set G) :=
      hXW.trans (W.le_centralizer.trans
        ((Subgroup.centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))
    have hdim := corank_of_direct_decomposition hgen hXN hdis hWcard
    rw [hf] at hdim
    subst n
    have hx := torusAction_of_rankOne_data h hU (d.le i) hn
      hXP hcyc hcard hgen hWcard hprod hreg
    refine ⟨X,regularSection_of_torus h ho hU (Or.inr hb) hWL hf ?_ ?_ hn hx⟩
    · simpa only [hf] using hgen
    · simpa only [hf] using hdis.eq_bot

omit [Finite G] in
private theorem cyclic_action_of_section {X : Subgroup G}
    (s : RegularCyclicSection M W U X) :
    ∃ x : Automizer W, x ∈ inducedAutomizer W (M ⊓ centralizer (U : Set G)) ∧
      orderOf x = 2 ^ subgroupCorank W U - 1 := by
  have hXN : X ≤ normalizer (W : Set G) :=
    s.contained.trans (inf_le_left.trans inf_le_right)
  let f : X →* Automizer W :=
    W.normalizerMonoidHom.rangeRestrict.comp (inclusion hXN)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have he : W.normalizerMonoidHom ⟨x,hXN x.property⟩ = 1 :=
      congrArg (fun a : Automizer W => (a : MulAut W)) hx
    have hc : (x : G) ∈ centralizer (W : Set G) := by
      have hk : (⟨x,hXN x.property⟩ : normalizer (W : Set G)) ∈
        W.normalizerMonoidHom.ker := he
      rwa [Subgroup.normalizerMonoidHom_ker] at hk
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (s.faithful ▸
      (show (x : G) ∈ X ⊓ centralizer (W : Set G) from ⟨x.property,hc⟩))
  let := s.cyclic
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := X)
  refine ⟨f x,?_,(orderOf_injective f hi x).trans (hx.trans s.card_eq)⟩
  exact ⟨⟨x,hXN x.property⟩,
    ⟨(s.contained x.property).1.1,(s.contained x.property).2⟩,rfl⟩

/-- The full cyclic-action conclusion at an actual minimum obstruction.
Both earlier structural inputs are supplied by their known-simple producers. -/
theorem doubledSeven_minimum_cyclic_action
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hU : U ∈ obstructionFamily M W)
    (hmin : (subgroupCorank W U : ℕ∞) = globalR W)
    (hn : 1 < subgroupCorank W U) :
    ∃ x : Automizer W, x ∈ inducedAutomizer W (M ⊓ centralizer (U : Set G)) ∧
      orderOf x = 2 ^ subgroupCorank W U - 1 := by
  obtain ⟨s⟩ := minimalRegularSection_of_source_models h
    (InvariantSubspaces.BlockSelection.e67Input_knownSimple h) hU hmin hn
    (fun L hL => (Components.RemainingSieve.adequateComponentAlternatives_knownSimple
      h hU hL).borel_symplectic_or_rank_one)
  exact cyclic_action_of_section s.regular

/-- The full cyclic actor at any maximal member of Γ. Both component and
characteristic-two block branches retain their literal relative placement. -/
theorem doubledSeven_maximal_cyclic_action
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hU : U ∈ obstructionFamily M W)
    (hmax : ∀ Y : Subgroup G, U < Y → Y ≤ W → centralizer (Y : Set G) ≤ M)
    (hn : 1 < subgroupCorank W U) :
    ∃ x : Automizer W, x ∈ inducedAutomizer W (M ⊓ centralizer (U : Set G)) ∧
      orderOf x = 2 ^ subgroupCorank W U - 1 := by
  obtain ⟨X,hX⟩ := maximal_regular_section h hU hmax hn
  exact cyclic_action_of_section hX

/-- A minimum obstruction of corank four or five is impossible for the
actual seven-letter automizer; the full image, including odd permutations,
is used here. -/
theorem doubledSeven_minimum_not_obstruction
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (e : Automizer W ≃* Equiv.Perm (Fin 7))
    (hmin : (subgroupCorank W U : ℕ∞) = globalR W)
    (hlo : 4 ≤ subgroupCorank W U) (hhi : subgroupCorank W U < 6) :
    U ∉ obstructionFamily M W := by
  intro hU
  obtain ⟨x,_,hx⟩ := doubledSeven_minimum_cyclic_action h hU hmin (by omega)
  have he : orderOf (e x) = 2 ^ subgroupCorank W U - 1 :=
    (orderOf_injective e.toMonoidHom e.injective x).trans hx
  have hc : subgroupCorank W U = 4 ∨ subgroupCorank W U = 5 := by omega
  rcases hc with hc | hc
  · rw [hc] at he
    exact doubledSeven_no_fifteen (e x) he
  · rw [hc] at he
    exact doubledSeven_no_thirtyOne (e x) he

end CFSG.Quasithin.Chapter7.NormalizedSource
