module

public import Stellmacher.SectionThree.LemmaThreeTwo
public import Stellmacher.SectionFour.LemmaFourOneCoreNormalizer

/-!
# Stellmacher (4.1): nonempty local families and their core normalizer

Under the Section 4 hypotheses, one of the two distinct maximal 2-local
subgroups containing the fixed Sylow subgroup `S` differs from `N_G(S)`.  Its
2-core is nontrivial because it is 2-local, and that core cannot equal `S`:
otherwise maximality would identify the subgroup with `N_G(S)`.  It therefore
lies in `LSet ⊤ S`.

Stellmacher (3.2) then makes `PSet ⊤ S` nonempty, since the 2-prime residual
of this local subgroup contains `S ≠ ⊥`.  The previously proved core-normalizer
part of (4.1) applies to that nonempty family and gives `O₂(M) ≠ 1` and
`N_G(S) ≤ M` for the paper's subgroup `M`.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (4.1).
-/

open scoped BigOperators

namespace Stellmacher.SectionFour

universe u

public structure LemmaFourOneConclusion
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) : Prop where
  part_a :
    SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅ ∧
      SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅
  part_b : twoCoreAmbient (mSubgroup S) ≠ ⊥
  part_c : Subgroup.normalizer (S : Set G) ≤ mSubgroup S

private theorem isSylowSubgroupIn_of_sylow_le
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M) :
    IsSylowSubgroupIn (S : Subgroup G) M := by
  refine ⟨S.subtype hSM, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSM]

private theorem twoCoreAmbient_ne_bot_of_twoLocal
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (hM : IsTwoLocal M) :
    twoCoreAmbient M ≠ ⊥ := by
  obtain ⟨Q, hQne, hQp, hMeq⟩ := hM
  have hQM : Q ≤ M := by
    rw [hMeq]
    exact Subgroup.le_normalizer
  have hQnormal : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 (by
      rw [hMeq])
  have hQpM : IsPGroup 2 (Q.subgroupOf M) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  have hQleCore : Q ≤ twoCoreAmbient M := by
    calc
      Q = (Q.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQM).symm
      _ ≤ (pCore 2 M).map M.subtype :=
        Subgroup.map_mono (le_sSup ⟨hQnormal, hQpM⟩)
      _ = twoCoreAmbient M := rfl
  intro hcore
  apply hQne
  exact le_bot_iff.mp (hQleCore.trans_eq hcore)

private theorem le_normalizer_twoCoreAmbient
    {G : Type u} [Group G] (M : Subgroup G) :
    M ≤ Subgroup.normalizer (twoCoreAmbient M : Set G) := by
  have hcoreM : twoCoreAmbient M ≤ M :=
    Subgroup.map_subtype_le (pCore 2 M)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreM).1
  unfold twoCoreAmbient
  rw [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

private theorem sylow_le_twoPrimeResidualAmbient
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M) :
    (S : Subgroup G) ≤ twoPrimeResidualAmbient M := by
  let T : Sylow 2 M := S.subtype hSM
  have hTmap : (T : Subgroup M).map M.subtype = (S : Subgroup G) := by
    dsimp [T]
    rw [Subgroup.map_subgroupOf_eq_of_le hSM]
  rw [← hTmap]
  exact Subgroup.map_mono
    (le_iSup (fun P : Sylow 2 M ↦ (P : Subgroup M)) T)

/-- **Stellmacher (4.1).** -/
public theorem lemma_four_one
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) :
    LemmaFourOneConclusion S := by
  obtain ⟨M₁, M₂, hMne, hM₁max, hM₂max, hSM₁, hSM₂⟩ :=
    h.two_distinct_maximal_twoLocal
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card h.even_order.two_dvd
  let N : Subgroup G := Subgroup.normalizer (S : Set G)
  have hNlocal : IsTwoLocal N := ⟨S, hSne, S.isPGroup', rfl⟩
  obtain ⟨M, hMmax, hSM, hMneN⟩ :
      ∃ M : Subgroup G,
        IsMaximalTwoLocal M ∧ (S : Subgroup G) ≤ M ∧ M ≠ N := by
    by_cases hM₁N : M₁ = N
    · exact ⟨M₂, hM₂max, hSM₂, fun hM₂N ↦ hMne (hM₁N.trans hM₂N.symm)⟩
    · exact ⟨M₁, hM₁max, hSM₁, hM₁N⟩
  have hMlocal : IsTwoLocal M := hMmax.prop
  have hCoreMne : twoCoreAmbient M ≠ ⊥ :=
    twoCoreAmbient_ne_bot_of_twoLocal M hMlocal
  have hSCoreM : (S : Subgroup G) ≠ twoCoreAmbient M := by
    intro hEq
    have hMN : M ≤ N := by
      dsimp [N]
      have hSet : (S : Set G) = (twoCoreAmbient M : Set G) :=
        congrArg (fun K : Subgroup G ↦ (K : Set G)) hEq
      rw [hSet]
      exact le_normalizer_twoCoreAmbient M
    exact hMneN (hMmax.eq_of_le hNlocal hMN)
  have hLM : M ∈ SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) :=
    ⟨le_top, isSylowSubgroupIn_of_sylow_le S M hSM, hCoreMne, hSCoreM⟩
  have hLnonempty :
      SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅ :=
    Set.Nonempty.ne_empty ⟨M, hLM⟩
  let hThree : SectionThree.Hypotheses G (S : Subgroup G) :=
    ⟨h.even_order, hSne, S.isPGroup'⟩
  have hPnonempty :
      SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅ := by
    intro hPempty
    have h32 := SectionThree.lemma_three_two (S : Subgroup G) hThree M hLM
    have hLocalPempty :
        SectionThree.PSet M (S : Subgroup G) = ∅ := by
      ext P
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hPM
      have hPtop :
          P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) :=
        ⟨⟨le_top, hPM.1.2⟩, hPM.2⟩
      rw [hPempty] at hPtop
      simp at hPtop
    have hResidualBot : twoPrimeResidualAmbient M = ⊥ := by
      rw [h32, hLocalPempty]
      simp
    apply hSne
    exact le_bot_iff.mp
      ((sylow_le_twoPrimeResidualAmbient S M hSM).trans_eq hResidualBot)
  obtain ⟨hCore, hNormalizer⟩ :=
    lemma_four_one_core_normalizer S h hPnonempty
  exact ⟨⟨hLnonempty, hPnonempty⟩, hCore, hNormalizer⟩

end Stellmacher.SectionFour
