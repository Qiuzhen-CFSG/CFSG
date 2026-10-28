module
public import Stellmacher.MainType.EightSix
public import Stellmacher.SectionEight.GeneratedEightSixObstruction
public import Stellmacher.SectionFiveToSeven.Result7_1
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

/-!
# A nonsolvable two-local in the Omega-eight-plus-three type

The source-local configuration (8.6)(c) has a native L3(2) normalizer quotient
for the join of two neighbor centers. Its direct-product equation puts the
initial center in D and hence in the next two-core. The intrinsic coset-graph
neighbor transitivity, together with normality of that core in its stabilizer,
puts the other neighbor center in the same two-core. Their join is therefore
a two-group and is nontrivial because the initial center has order four.

The L3(2) quotient makes the native normalizer nonsolvable. Injective embedding
into the ambient group then produces an ambient nonsolvable two-local. This
uses only the type data and intrinsic graph laws: no Section Seven or global
Hypothesis Two assumption is added to the source-local type predicate.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(c1,c4), printed
p.41, the type definition on p.45, and the last assertion of Theorem 1.
-/

namespace Stellmacher
open Later SectionsFiveToSeven CosetGraphContext SectionEight
universe u

public theorem IsOfOmegaEightPlusThreeType.exists_nonsolvable_twoLocal
    {H : Type u} [Group H] [Finite H]
    (h : IsOfOmegaEightPlusThreeType H) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  obtain ⟨d⟩ := h
  let _ := d.groupK
  let _ := d.finiteK
  obtain ⟨lam,hlam,_hlam_ne,hmodel⟩ := d.caseC.normalizer_quotient
  have hZaD : ZAt d.Γ d.criticalPath.a ≤ d.D := by
    rw [d.caseC.initial_core.2.2.2.1]
    exact le_sup_right
  have hDnext : d.D ≤ QAt d.Γ d.criticalPath.firstStep := by
    rw [d.caseC.definitions.1]
    exact inf_le_right
  have hZaQ := hZaD.trans hDnext
  have ha : d.criticalPath.a ∈ Neighborhood d.Γ d.criticalPath.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent d.Γ).mpr
      (d.Γ.adjacent_symm d.criticalPath.firstStep_adj)
  obtain ⟨g,hg⟩ := (lemma_seven_one_graph d.Γ).local_transitivity
    d.criticalPath.firstStep ha hlam
  have hQmap : (QAt d.Γ d.criticalPath.firstStep).map
      (MulAut.conj ((g : d.K)⁻¹)).toMonoidHom = QAt d.Γ d.criticalPath.firstStep :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt d.Γ d.criticalPath.firstStep : Set d.K)).inv_mem
        (SevenSix.stabilizer_le_normalizer_q d.Γ d.criticalPath.firstStep g.property))
  have hlamQ : ZAt d.Γ lam ≤ QAt d.Γ d.criticalPath.firstStep := by
    rw [← hg]
    change z d.Γ (d.Γ.act (g : d.K) d.criticalPath.a) ≤ _
    rw [z_act]
    exact (Subgroup.map_mono hZaQ).trans_eq hQmap
  have hcore : ZAt d.Γ lam ⊔ ZAt d.Γ d.criticalPath.a ≤
      QAt d.Γ d.criticalPath.firstStep := sup_le hlamQ hZaQ
  have htwo : IsPGroup 2 (QAt d.Γ d.criticalPath.firstStep) := by
    change IsPGroup 2 (d.Γ.twoCoreAt d.criticalPath.firstStep)
    rw [d.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hne : ZAt d.Γ lam ⊔ ZAt d.Γ d.criticalPath.a ≠ ⊥ := by
    intro hbot
    have hZa : ZAt d.Γ d.criticalPath.a = ⊥ :=
      bot_unique (le_sup_right.trans_eq hbot)
    have hcard := d.caseC.initial_core.2.2.1
    rw [hZa,Subgroup.card_bot] at hcard
    norm_num at hcard
  exact ambient_bad_local_of_psl3_two_normalizer_quotient
    d.embedding d.embedding_injective _ hne (htwo.to_le hcore) hmodel

end Stellmacher
