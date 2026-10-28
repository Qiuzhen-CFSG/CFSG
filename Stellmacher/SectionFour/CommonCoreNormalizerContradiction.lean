module

public import Stellmacher.SectionFour.LemmaFourOne

/-!
# The common-core normalizer contradiction in Stellmacher (4.6)

Under the exact Section Four hypotheses and two-family cover, the centralizer
`C = cSubgroup S` cannot normalize the two-core of the actual subgroup
`M = mSubgroup S`. This closes the final paragraph of (4.6) once its Hall
argument gives normalization of the identified common partner core.

Set `N = N_G(O₂(M))`. By (4.1), its defining two-core is nontrivial, making
`N` a 2-local subgroup. Normality of the core and (4.1) also put `M` and
`N_G(S)` in `N`. The hypothesized containment of `C`, together with the
cover, puts every member of the global local family in `N`. For any 2-local
subgroup `L` containing `S`, either `O₂(L) = S`, or (3.2) puts the two-prime
residual of `L` in `N`. In the latter case the normalizer factorization
supplies the rest of `L` from `N_G(S)`. Thus every such `L` lies in `N`,
and the two supplied distinct maximal 2-local subgroups both equal `N`.

The proof uses the same local-generation reduction as `OutsideMember`, now
with target `N`, and requires neither maximality of `M` nor `N = M`.
Source: refs/latex/stellmacher-n-group.tex, final paragraph of (4.6), journal
page 26, using (3.2), (4.1), and the Section Four standing hypotheses.
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

/-- The two-family cover prevents `C` from normalizing the actual core of `M`. -/
public theorem four_six_contradiction_of_core_normalized_by_c
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (mSubgroup S) (S : Subgroup G))
    (hC : cSubgroup S ≤
      Subgroup.normalizer (twoCoreAmbient (mSubgroup S) : Set G)) : False := by
  have h41 := lemma_four_one S h
  let N := Subgroup.normalizer (twoCoreAmbient (mSubgroup S) : Set G)
  have hNlocal : IsTwoLocal N :=
    ⟨twoCoreAmbient (mSubgroup S), h41.part_b,
      (pCore_isPGroup (p := 2) (G := mSubgroup S)).map (mSubgroup S).subtype, rfl⟩
  have hMN : mSubgroup S ≤ N := le_normalizer_core (mSubgroup S)
  have hSN : Subgroup.normalizer (S : Set G) ≤ N := h41.part_c.trans hMN
  have hall : ∀ P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G), P ≤ N := by
    intro P hP
    rw [hcover] at hP
    rcases hP with hP | hP
    · exact hP.1.1.trans hC
    · exact hP.1.1.trans hMN
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card h.even_order.two_dvd
  have hThree : SectionThree.Hypotheses G (S : Subgroup G) :=
    ⟨h.even_order, hSne, S.isPGroup'⟩
  have hlocal_le (L : Subgroup G) (hLlocal : IsTwoLocal L)
      (hSL : (S : Subgroup G) ≤ L) : L ≤ N := by
    have hSyl : IsSylowSubgroupIn (S : Subgroup G) L := by
      refine ⟨S.subtype hSL, ?_⟩
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSL]
    by_cases heq : (S : Subgroup G) = twoCoreAmbient L
    · exact (show L ≤ Subgroup.normalizer (S : Set G) by
        rw [show (S : Set G) = (twoCoreAmbient L : Set G) from
          congrArg (fun K : Subgroup G ↦ (K : Set G)) heq]
        exact le_normalizer_core L).trans hSN
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
      have hres : twoPrimeResidualAmbient L ≤ N := by
        rw [SectionThree.lemma_three_two (S : Subgroup G) hThree L hLL]
        refine iSup_le fun P ↦ ?_
        exact hall P.1 ⟨⟨le_top, P.2.1.2⟩, P.2.2⟩
      obtain ⟨N, _, _, hNnorm, hLN⟩ :=
        SectionThree.exists_normalizer_factor L (S : Subgroup G) hSyl
      exact hLN.trans (sup_le hres (hNnorm.trans hSN))
  obtain ⟨M₁, M₂, hne, hmax₁, hmax₂, hSM₁, hSM₂⟩ :=
    h.two_distinct_maximal_twoLocal
  have heq₁ : M₁ = N :=
    hmax₁.eq_of_le hNlocal (hlocal_le M₁ hmax₁.prop hSM₁)
  have heq₂ : M₂ = N :=
    hmax₂.eq_of_le hNlocal (hlocal_le M₂ hmax₂.prop hSM₂)
  exact hne (heq₁.trans heq₂.symm)

end Stellmacher.SectionFour
