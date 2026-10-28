module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.AtMostOneCenter
public import Theory.Quasithin.ProductLocalRank
/-!
# Source rank transfer with one centered direct factor

The original failure witness forces a nontrivial component center. If the
ambient group is the direct product of that component and a centerless
complement, its center has order three. The original offending section is
therefore the central quotient. Proper-section induction bounds the ranks
of the component quotient, and the direct-product formula transfers these
bounds to the actual section, contradicting the failure of Theorem A.

The only retained structural input is the actual complement decomposition;
the next source assembly constructs it from uniqueness of the centered
component. Source: Aschbacher–Smith A.2.12(III), printed p.37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.source_exists_centered_component
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremAOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) :
    ∃ C : Subgroup G, IsComponent G C ∧ center C ≠ ⊥ := by
  by_contra! hall
  have hz : center G = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hpw := center_pow_eq_one_of_component_centers hsemi 1
      (fun C hC z hz => by simpa [hall C hC] using hz) x hx
    simpa using hpw
  have hd := h.prime_dvd_center_of_semisimple ih hsemi
  rw [hz] at hd
  exact h.2.2.2.2.1.not_dvd_one (by simpa using hd)

theorem CounterexampleToTheoremA.source_not_one_centered_direct_product
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    {C : Subgroup G} (hC : IsComponent G C) (hzC : center C ≠ ⊥)
    {B : Type u} [Group B] [Finite B] (hzB : center B = ⊥)
    (hB : ∃ M : Subgroup B, IsTwoLocal M) (e : G ≃* C × B) : False := by
  have hp := h.source_semisimple_prime_eq_three ih hsemi hn
  subst p
  let := hC.2
  have hc : Nat.card (center C) = 3 := h.component_center_card_three ih hsemi hn
    SQTKStructure.OrdinarySource.remainingOddCoverInputs hC hzC
  have hg : Nat.card (center G) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv, Subgroup.center_prod,
      Nat.card_congr ((center C).prodEquiv (center B)).toEquiv, Nat.card_prod, hzB]
    simpa using hc
  obtain ⟨es⟩ := h.section_equiv_centerQuotient_of_center_card_three ih.theoremA hsemi hg
  have hcp : C ≠ ⊤ := by
    intro ht
    let : IsQuasisimple (⊤ : Subgroup G) := ht ▸ hC.2
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  have hmodel := component_centralQuotient_models_of_semisimple_not_quasisimple
    ih h.1 h.2.1 hsemi hn hC
  have hqsemi : IsSemisimple (C ⧸ center C) := by
    apply componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center C))
      (QuotientGroup.mk'_surjective _)
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup C).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).symm⟩
  have hlc := (ih.subgroup C hcp).1.localRanks_of_stronglyQuasithin hmodel.1
    (h.2.1.subgroup C) (IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center C)))
    hqsemi 3 Nat.prime_three (by decide)
  have hrc : primeRank 3 (C ⧸ center C) ≤ primeRank 3 C := by
    obtain ⟨h1, h2⟩ := h.source_component_threeRanks_eq_two ih hsemi hn hC hzC
    omega
  let π : C × B →* (C ⧸ center C) × B :=
    (QuotientGroup.mk' (center C)).prodMap (MonoidHom.id B)
  have hπ : Function.Surjective π := by
    rintro ⟨a,b⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center C) a
    exact ⟨(c,b), rfl⟩
  have hk : π.ker = center (C × B) := by
    ext x
    change (QuotientGroup.mk' (center C) x.1, x.2) = (1,1) ↔ x ∈ center (C × B)
    rw [Prod.mk.injEq, Subgroup.center_prod, mem_prod, hzB]
    exact and_congr (QuotientGroup.eq_one_iff x.1) Iff.rfl
  let f := π.comp e.toMonoidHom
  have hf : Function.Surjective f := hπ.comp e.surjective
  have hfk : f.ker = center G := by
    ext x
    change π (e x) = 1 ↔ x ∈ center G
    rw [← MonoidHom.mem_ker, hk]
    exact MulEquivClass.apply_mem_center_iff e
  let eqc : G ⧸ center G ≃* (C ⧸ center C) × B :=
    QuotientGroup.liftEquiv (center G) hf hfk.symm
  obtain ⟨Q, hQp, hQ⟩ := hC.exists_nontrivial_two_subgroup
  have hctwo : ∃ M : Subgroup C, IsTwoLocal M :=
    ⟨normalizer (Q : Set C), Q, hQ, hQp, rfl⟩
  have hl := Theory.Quasithin.ProductLocalRank.local_prod_le_of_factor_ranks
    3 hctwo hB hrc hlc
  have hr : primeRank 3 ((C ⧸ center C) × B) ≤ primeRank 3 (C × B) := by
    rw [primeRank_prod_eq_add, primeRank_prod_eq_add]
    exact Nat.add_le_add_right hrc _
  apply h.2.2.2.2.2.2
  refine ⟨Or.inl ⟨?_, isQuasithin_iff_twoLocalPrimeRank.mp h.1 3 Nat.prime_three (by decide)⟩,
    fun _ => ?_⟩
  · rw [twoLocalPrimeRank_mulEquiv 3 (es.trans eqc), twoLocalPrimeRank_mulEquiv 3 e]
    exact hl
  · rw [primeRank_equiv 3 (es.trans eqc), primeRank_equiv 3 e]
    exact hr

end CFSG.Quasithin.ChapterA.Section02
