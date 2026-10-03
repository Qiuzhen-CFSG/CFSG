module

public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionEight.LemmaEightTwo
public import Stellmacher.ExceptionalType

/-!
# The noncentral Section Eight local types

For a Sylow terminal context, (8.2) identifies each critical-edge stabilizer
as S4 or C2 times S4. Restriction equivalences recover the ambient local
subgroups. Their common Sylow subgroup has order eight or sixteen, excluding
mixed models. Its index in either local subgroup is three; any larger
intersection would identify the two local groups, contradicting the trivial
two-core of their join. The resulting pair realizes exactly the L3(2) or
Sp4(2) local type, with the original ambient Sylow as intersection.

Source: `refs/latex/stellmacher-n-group.tex`, (8.2), the definitions following
it, and the multiple-maximal reduction at the start of Section Eleven.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven Later

universe u

private theorem factorization_twenty_four : (24 : ℕ).factorization 2 = 3 := by
  rw [show 24 = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

private theorem factorization_forty_eight : (48 : ℕ).factorization 2 = 4 := by
  rw [show 48 = 2 ^ 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

private theorem sylow_card_from_model
    {H : Type u} [Group H] [Finite H]
    {S P : Subgroup H} (hSylow : IsSylowTwoIn S P)
    {Model : Type*} [Group Model] [Finite Model]
    (hModel : IsModel P Model) : Nat.card S = 2 ^ (Nat.card Model).factorization 2 := by
  obtain ⟨_, sylow, hsylow⟩ := hSylow
  obtain ⟨model⟩ := hModel
  rw [← hsylow, Subgroup.card_map_of_injective P.subtype_injective,
    sylow.card_eq_multiplicity, Nat.card_congr model.toEquiv]

private theorem model_pair_same
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (hS1 : IsSylowTwoIn S P1) (hS2 : IsSylowTwoIn S P2)
    (hP1 : IsModel P1 S4 ∨ IsModel P1 (C2 × S4))
    (hP2 : IsModel P2 S4 ∨ IsModel P2 (C2 × S4)) :
    (IsModel P1 S4 ∧ IsModel P2 S4) ∨
      (IsModel P1 (C2 × S4) ∧ IsModel P2 (C2 × S4)) := by
  have hS4 : Nat.card S4 = 24 := by
    norm_num [S4, Nat.card_eq_fintype_card, Fintype.card_perm]
  have hC2S4 : Nat.card (C2 × S4) = 48 := by
    rw [Nat.card_prod, hS4]
    norm_num [C2, Nat.card_eq_fintype_card]
  rcases hP1 with hP1 | hP1 <;> rcases hP2 with hP2 | hP2
  · exact Or.inl ⟨hP1, hP2⟩
  · have hfirst := sylow_card_from_model hS1 hP1
    have hsecond := sylow_card_from_model hS2 hP2
    rw [hS4, factorization_twenty_four] at hfirst
    rw [hC2S4, factorization_forty_eight] at hsecond
    omega
  · have hfirst := sylow_card_from_model hS1 hP1
    have hsecond := sylow_card_from_model hS2 hP2
    rw [hC2S4, factorization_forty_eight] at hfirst
    rw [hS4, factorization_twenty_four] at hsecond
    omega
  · exact Or.inr ⟨hP1, hP2⟩

private theorem intersection_of_index_three
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (hS1 : S ≤ P1) (hS2 : S ≤ P2)
    (hindex : S.relIndex P1 = 3)
    (hcard : Nat.card P1 = Nat.card P2)
    (hne : P1 ≠ P2) : P1 ⊓ P2 = S := by
  have hSI : S ≤ P1 ⊓ P2 := le_inf hS1 hS2
  have hmul := Subgroup.relIndex_mul_relIndex S (P1 ⊓ P2) P1 hSI inf_le_left
  rw [hindex] at hmul
  have hdiv : S.relIndex (P1 ⊓ P2) ∣ 3 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hSI
  · rw [hthree] at hmul
    have hone : (P1 ⊓ P2).relIndex P1 = 1 := by omega
    have hle : P1 ≤ P2 := (Subgroup.relIndex_eq_one.mp hone).trans inf_le_right
    exact (hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)).elim

private theorem model_pair_intersection
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 (S0 : Subgroup H) P1 P2)
    (hmodel : (IsModel P1 S4 ∧ IsModel P2 S4) ∨
      (IsModel P1 (C2 × S4) ∧ IsModel P2 (C2 × S4))) :
    P1 ⊓ P2 = (S0 : Subgroup H) := by
  have hne : P1 ≠ P2 := by
    intro heq
    have hcore := h.fiveOne.join_twoCore_eq_bot
    rw [heq, sup_idem] at hcore
    exact h.fiveOne.P2_mem.1.2.2.1 hcore
  have hmul := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup H)
    (S0 : Subgroup H) P1 bot_le h.fiveOne.P1_mem.1.2.1.1
  simp only [Subgroup.relIndex_bot_left] at hmul
  rcases hmodel with ⟨⟨first⟩, ⟨second⟩⟩ | ⟨⟨first⟩, ⟨second⟩⟩
  · have hP1 : Nat.card P1 = 24 := by
      rw [Nat.card_congr first.toEquiv]
      norm_num [S4, Nat.card_eq_fintype_card, Fintype.card_perm]
    have hP2 : Nat.card P2 = Nat.card P1 :=
      Nat.card_congr (second.trans first.symm).toEquiv
    have hS := sylow_card_from_model h.fiveOne.P1_mem.1.2.1 ⟨first⟩
    rw [← Nat.card_congr first.toEquiv, hP1, factorization_twenty_four] at hS
    apply intersection_of_index_three h.fiveOne.P1_mem.1.2.1.1
      h.fiveOne.P2_mem.1.2.1.1 _ hP2.symm hne
    rw [hP1, hS] at hmul
    omega
  · have hP1 : Nat.card P1 = 48 := by
      rw [Nat.card_congr first.toEquiv, Nat.card_prod]
      norm_num [C2, S4, Nat.card_eq_fintype_card, Fintype.card_perm]
    have hP2 : Nat.card P2 = Nat.card P1 :=
      Nat.card_congr (second.trans first.symm).toEquiv
    have hS := sylow_card_from_model h.fiveOne.P1_mem.1.2.1 ⟨first⟩
    rw [← Nat.card_congr first.toEquiv, hP1, factorization_forty_eight] at hS
    apply intersection_of_index_three h.fiveOne.P1_mem.1.2.1.1
      h.fiveOne.P2_mem.1.2.1.1 _ hP2.symm hne
    rw [hP1, hS] at hmul
    omega

public theorem multiple_eight_two_terminal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ ≠ ⊥)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    IsOfL3TwoType H ∨ IsOfSp4TwoType H := by
  have hmodels := SectionEight.lemma_eight_two_local
    (ctx.toSectionEightContext hcomm).toLocalContext hcenter
  have ha := hmodels ctx.criticalPath.a
  have hb := hmodels ctx.criticalPath.firstStep
  change IsModel (GAt ctx.Γ ctx.criticalPath.a) S4 ∨
    IsModel (GAt ctx.Γ ctx.criticalPath.a) (C2 × S4) at ha
  change IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) S4 ∨
    IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) (C2 × S4) at hb
  have hbase :
      (IsModel (P1.subgroupOf (P1 ⊔ P2)) S4 ∨
        IsModel (P1.subgroupOf (P1 ⊔ P2)) (C2 × S4)) ∧
      (IsModel (P2.subgroupOf (P1 ⊔ P2)) S4 ∨
        IsModel (P2.subgroupOf (P1 ⊔ P2)) (C2 × S4)) := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · exact ⟨by simpa [GAt, hedge.1] using ha, by simpa [GAt, hedge.2] using hb⟩
    · exact ⟨by simpa [GAt, hedge.2] using hb, by simpa [GAt, hedge.1] using ha⟩
  have hP1 : IsModel P1 S4 ∨ IsModel P1 (C2 × S4) :=
    hbase.1.imp
      (fun ⟨model⟩ => ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans model⟩)
      (fun ⟨model⟩ => ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans model⟩)
  have hP2 : IsModel P2 S4 ∨ IsModel P2 (C2 × S4) :=
    hbase.2.imp
      (fun ⟨model⟩ => ⟨(Subgroup.subgroupOfEquivOfLe le_sup_right).symm.trans model⟩)
      (fun ⟨model⟩ => ⟨(Subgroup.subgroupOfEquivOfLe le_sup_right).symm.trans model⟩)
  have hpair := model_pair_same ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1
    ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1 hP1 hP2
  let pair : LocalTypePair H := {
    sylowIntersection := S0
    first := P1
    second := P2
    intersection_eq := model_pair_intersection ctx.hypothesisTwo hpair
    join_twoCore_eq_bot := ctx.sectionSeven.twoCore_eq_bot }
  rcases hpair with hpair | hpair
  · exact Or.inl ⟨pair, hpair⟩
  · exact Or.inr ⟨pair, hpair⟩

end Stellmacher.SectionEleven
