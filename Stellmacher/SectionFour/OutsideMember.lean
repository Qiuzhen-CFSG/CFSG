module

public import Stellmacher.SectionFour.LemmaFourOne

/-!
# A local-family member outside the core normalizer

Under the Section 4 hypotheses, the global family `PSet ⊤ S` has a member
outside the family restricted to `M = N_G(D)`. This supplies the implicit
existence assertion at the start of the proof of (4.6).

Otherwise (3.2) puts the 2-prime residual of every local overgroup of `S`
inside `M`. The Frattini factorization and (4.1)'s `N_G(S) ≤ M` then put
every maximal 2-local overgroup of `S` in `M`. If its 2-core equals `S`,
normality gives this containment directly. The group `M` normalizes its
nontrivial 2-core, so both given maximal overgroups lie in the same 2-local
normalizer and hence are equal, contrary to the hypotheses.

Source: `refs/latex/stellmacher-n-group.tex`, opening of (4.6), using (3.2),
(4.1), and the Section 4 hypotheses.
-/

namespace Stellmacher.SectionFour

universe u

private theorem le_normalizer_core
    {G : Type u} [Group G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 L))).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- The global local family cannot be contained in the family over `M`. -/
public theorem exists_pSet_not_mem_mSubgroup
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    ∃ P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G),
      P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G) := by
  classical
  by_contra hnone
  have hall : ∀ P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G),
      P ∈ SectionThree.PSet (mSubgroup S) (S : Subgroup G) := by
    intro P hP
    by_contra hPM
    exact hnone ⟨P, hP, hPM⟩
  have h41 := lemma_four_one S h
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card h.even_order.two_dvd
  have hThree : SectionThree.Hypotheses G (S : Subgroup G) :=
    ⟨h.even_order, hSne, S.isPGroup'⟩
  have hlocal_le (L : Subgroup G) (hLlocal : IsTwoLocal L)
      (hSL : (S : Subgroup G) ≤ L) : L ≤ mSubgroup S := by
    have hSyl : IsSylowSubgroupIn (S : Subgroup G) L := by
      refine ⟨S.subtype hSL, ?_⟩
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSL]
    by_cases heq : (S : Subgroup G) = twoCoreAmbient L
    · exact (show L ≤ Subgroup.normalizer (S : Set G) by
        rw [show (S : Set G) = (twoCoreAmbient L : Set G) from
          congrArg (fun K : Subgroup G ↦ (K : Set G)) heq]
        exact le_normalizer_core L).trans h41.part_c
    · have hcore : twoCoreAmbient L ≠ ⊥ := by
        obtain ⟨Q, hQne, hQp, hLQ⟩ := hLlocal
        have hQL : Q ≤ L := by rw [hLQ]; exact Subgroup.le_normalizer
        have hQN : (Q.subgroupOf L).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr (by rw [hLQ])
        have hQpL : IsPGroup 2 (Q.subgroupOf L) :=
          hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
        have hQcore : Q ≤ twoCoreAmbient L := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hQL]
          exact Subgroup.map_mono (le_sSup ⟨hQN, hQpL⟩)
        intro hbot
        exact hQne (le_bot_iff.mp (hQcore.trans_eq hbot))
      have hLL : L ∈ SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) :=
        ⟨le_top, hSyl, hcore, heq⟩
      have hres : twoPrimeResidualAmbient L ≤ mSubgroup S := by
        rw [SectionThree.lemma_three_two (S : Subgroup G) hThree L hLL]
        refine iSup_le fun P ↦ ?_
        exact (hall P.1 ⟨⟨le_top, P.2.1.2⟩, P.2.2⟩).1.1
      obtain ⟨N, _, _, hNnorm, hLN⟩ :=
        SectionThree.exists_normalizer_factor L (S : Subgroup G) hSyl
      exact hLN.trans (sup_le hres (hNnorm.trans h41.part_c))
  let N : Subgroup G := Subgroup.normalizer (twoCoreAmbient (mSubgroup S) : Set G)
  have hNlocal : IsTwoLocal N :=
    ⟨twoCoreAmbient (mSubgroup S), h41.part_b,
      (pCore_isPGroup (p := 2) (G := mSubgroup S)).map (mSubgroup S).subtype, rfl⟩
  have hMN : mSubgroup S ≤ N := le_normalizer_core (mSubgroup S)
  obtain ⟨M₁, M₂, hne, hmax₁, hmax₂, hSM₁, hSM₂⟩ :=
    h.two_distinct_maximal_twoLocal
  have heq₁ : M₁ = N :=
    hmax₁.eq_of_le hNlocal ((hlocal_le M₁ hmax₁.prop hSM₁).trans hMN)
  have heq₂ : M₂ = N :=
    hmax₂.eq_of_le hNlocal ((hlocal_le M₂ hmax₂.prop hSM₂).trans hMN)
  exact hne (heq₁.trans heq₂.symm)

end Stellmacher.SectionFour
