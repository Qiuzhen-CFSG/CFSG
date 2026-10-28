module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Actions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
/-!
# Lifting the ordinary rank-one quotient

The PSL₂ order formula excludes the central covers of PSL₃(4) and G₂(4).
The odd linear alternatives are centerless, and PSL₃(3) has incompatible
order. Together with the alternating-action exclusions this leaves the
characteristic-two simple case and the Fermat/Mersenne PSL₂ case, provided
the remaining sporadic models have been separated. Equality of the odd
PSL₂ parameters preserves the parameter already supplied by the source.

The two comparison premises below are explicit unfinished prerequisites,
not assertions of the source classification. The parent module owns their
instantiation and the final rank-one conclusion.

Source: Aschbacher–Smith, 1.1.5(3), printed pp.501–503, and the proof of
15.4.20, printed p.1164.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
open ClassificationModels Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {L : Type u} [Group L]

/-- Perfect nontrivial odd PSL₂ groups have the required lower parameter bound. -/
theorem odd_parameter_ge_five [Nontrivial L] [Group.IsPerfect L] {p : ℕ}
    (hp : Odd p) (hm : ClassicalGroup.IsPSL L 2 p) : 5 ≤ p := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hn : ¬ Group.IsSolvable PSL(2,F) := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable L
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hh := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    (hF ▸ hp) hn
  obtain ⟨k,hk⟩ := hp
  omega

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hh : 2 ≤ 2^(2^k) := Nat.le_pow (by positivity)
    omega
  · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
    have hh := dvd_pow_self 2 hk0
    rw [← hk] at hh
    norm_num at hh

private theorem simple_perfect_center [IsSimpleGroup L] [Group.IsPerfect L] :
    center L = ⊥ := by
  rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim

private theorem not_linear_three {q : ℕ} (hq : q = 3 ∨ q = 4)
    (hm : RankOneQuotientModel L) (h3 : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 q) :
    False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h3
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  rcases hm with ⟨_,_,hm⟩ | ⟨_,_,_,hm⟩ <;> rcases hq with rfl | rfl
  · norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_5616 hm (by omega)
  · norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_20160 hm (by omega)
  · norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_5616 hm (by omega)
  · norm_num [Fin.prod_univ_succ] at hc
    exact psl_two_card_ne_20160 hm (by omega)

private theorem not_g2_four (hm : RankOneQuotientModel L)
    (hG2 : IsG2At (L ⧸ pCore 2 L) 4) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hG2
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at hc
  norm_num at hc
  rcases hm with ⟨_,_,hm⟩ | ⟨_,_,_,hm⟩ <;>
    exact psl_two_card_ne_of_gaps (c := 251596800) (a := 631) (b := 795) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc

/-- The two central-cover alternatives are incompatible with the source quotient. -/
theorem not_two_cover_model (hm : RankOneQuotientModel L)
    (hc : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨ IsG2At (L ⧸ pCore 2 L) 4) :
    False := by
  rcases hc with hc | hc
  · exact not_linear_three (Or.inr rfl) hm hc
  · exact not_g2_four hm hc

/-- After the concrete exclusions, the seed is centerless and belongs to
one of the two remaining actual simple-model families. -/
theorem surviving_model_of_action
    (hspor : ∀ (name : SporadicName) {q : ℕ}, name ≠ .j3 →
      ((∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) →
      ¬ ClassicalGroup.IsPSL name.Carrier 2 q)
    [IsQuasisimple L] (hm : RankOneQuotientModel L)
    (hcenter : center L = pCore 2 L) {α : MulAut L} (ha : ModelAction115 L α) :
    center L = ⊥ ∧ (LieTypeTwoModel L ∨
      ∃ q : ℕ, IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL L 2 q) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  cases ha with
  | lie hs hlie _ =>
    let := hs
    exact ⟨simple_perfect_center, Or.inl hlie⟩
  | two_cover _ _ hc _ => exact (not_two_cover_model hm hc).elim
  | six σ _ ha => exact (not_alternating_action hm hcenter (Or.inl rfl) σ ha).elim
  | seven σ _ ha => exact (not_alternating_action hm hcenter (Or.inr rfl) σ ha).elim
  | odd hodd _ =>
    rcases hodd with h3 | ⟨q,hq,hqmodel⟩
    · have hc : center L = ⊥ := by
        obtain ⟨F,_,_,_,⟨e⟩⟩ := h3
        let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
        let : IsSimpleGroup L := e.isSimpleGroup
        exact simple_perfect_center
      have hcore := hcenter.symm.trans hc
      let e : (L ⧸ pCore 2 L) ≃* L :=
        (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
      exact (not_linear_three (Or.inl rfl) hm (h3.of_mulEquiv e)).elim
    · have hq5 := odd_parameter_ge_five (fermat_mersenne_odd hq) hqmodel
      have hc : center L = ⊥ := by
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hqmodel
        let : IsSimpleGroup PSL(2,F) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
        let : IsSimpleGroup L := e.isSimpleGroup
        exact simple_perfect_center
      exact ⟨hc, Or.inr ⟨q,hq,hqmodel⟩⟩
  | sporadic name hne he _ =>
    obtain ⟨e⟩ := he
    rcases hm with ⟨n,hn,hm⟩ | ⟨p,hp,ho,hm⟩
    · exact (hspor name hne (Or.inl ⟨n,hn,rfl⟩) (hm.of_mulEquiv e.symm)).elim
    · exact (hspor name hne (Or.inr ⟨hp,ho⟩) (hm.of_mulEquiv e.symm)).elim

/-- Conditional assembly of the actual seed model, retaining its given even
exponent or odd prime. Both external comparisons still have to be proved. -/
theorem ordinary_model_of_comparisons
    (hlie : ∀ {Q : Type u} [Group Q] [Finite Q] {p : ℕ}, p.Prime → Odd p → 5 ≤ p →
      ClassicalGroup.IsPSL Q 2 p → LieTypeTwoModel Q → IsFermatOrMersennePrime p)
    (hspor : ∀ (name : SporadicName) {q : ℕ}, name ≠ .j3 →
      ((∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) →
      ¬ ClassicalGroup.IsPSL name.Carrier 2 q)
    [Finite L] [IsQuasisimple L] (hm : RankOneQuotientModel L)
    (hcenter : center L = pCore 2 L) {α : MulAut L} (ha : ModelAction115 L α) :
    OrdinaryRankOneModel L := by
  obtain ⟨hc,hs⟩ := surviving_model_of_action hspor hm hcenter ha
  have hcore := hcenter.symm.trans hc
  let e : L ≃* (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm
  rcases hm with ⟨n,hn,hm⟩ | ⟨p,hp,ho,hm⟩
  · have hmodel := hm.of_mulEquiv e
    exact Or.inr ⟨n,hn,even_exponent_ge_two hn hmodel,hmodel⟩
  · have hmodel := hm.of_mulEquiv e
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    have hp5 := odd_parameter_ge_five ho hmodel
    refine Or.inl ⟨p,?_,hp5,hmodel⟩
    rcases hs with hs | ⟨q,hq,hqm⟩
    · exact hlie hp ho hp5 hmodel hs
    · have heq := odd_parameter_unique ho (fermat_mersenne_odd hq) hmodel hqm
      simpa only [heq] using hq
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
