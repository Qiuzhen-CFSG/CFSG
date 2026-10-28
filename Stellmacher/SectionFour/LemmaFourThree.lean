module

public import Stellmacher.SectionFour.LemmaFourOne
public import Stellmacher.SectionFour.LemmaFourTwo

/-!
# Stellmacher's Lemma 4.3

The global intersection `dSubgroup S` may be restricted to either of the
families `pZero S` and `pOne S`.  These are the two families denoted
`P₀(S)` and `P₁(S)` in the source, formed using respectively
`C = C_G(Ω₁(Z(S)))` and `M = N_G(D)`.

For a general subgroup `M` with nontrivial 2-core, the proof compares
`PStarSet L S` for every maximal `L ∈ LSet ⊤ S` with the union of
`PStarSet M S` and the globally starred members outside `PSet M S`.  A member
inside `PSet M S` makes `M` itself a member of `LSet ⊤ S`, so Lemma 4.2
identifies the starred and unstarred core intersections there.  A member
outside is directly present in the second half of the union.  Lemma 4.2's
maximal-`LSet` formula then gives the desired global equality.

For `M = N_G(D)`, nontriviality of its 2-core is Lemma 4.1(b).  For the
centralizer `C`, the nontrivial group `Z = Ω₁(Z(S))` is a normal 2-subgroup
of `C`, hence lies in `O₂(C)`.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (4.3),
journal page 25.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionFour

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem pSet_top_of_pSet
    {S U P : Subgroup G} (hP : P ∈ SectionThree.PSet U S) :
    P ∈ SectionThree.PSet (⊤ : Subgroup G) S :=
  ⟨⟨le_top, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩

omit [Finite G] in
private theorem sylow_le_of_isSylowSubgroupIn
    {S P : Subgroup G} (hSylow : IsSylowSubgroupIn S P) : S ≤ P := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_subtype_le (T : Subgroup P)

omit [Finite G] in
private theorem isSylowSubgroupIn_of_sylow_le
    (S : Sylow 2 G) (M : Subgroup G) (hSM : (S : Subgroup G) ≤ M) :
    IsSylowSubgroupIn (S : Subgroup G) M := by
  refine ⟨S.subtype hSM, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSM]

omit [Finite G] in
private theorem twoCoreAmbient_le_sylowImage
    {S P : Subgroup G} (hSylow : IsSylowSubgroupIn S P) :
    twoCoreAmbient P ≤ S := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)

omit [Finite G] in
private theorem twoCoreAmbient_le_of_le_of_common_sylow
    (L P S : Subgroup G) (hPL : P ≤ L)
    (hSylL : IsSylowSubgroupIn S L)
    (hSylP : IsSylowSubgroupIn S P) :
    twoCoreAmbient L ≤ twoCoreAmbient P := by
  have hCoreLS : twoCoreAmbient L ≤ S :=
    twoCoreAmbient_le_sylowImage hSylL
  have hSP : S ≤ P := sylow_le_of_isSylowSubgroupIn hSylP
  have hCoreLP : twoCoreAmbient L ≤ P := hCoreLS.trans hSP
  have hCoreLL : twoCoreAmbient L ≤ L :=
    Subgroup.map_subtype_le (pCore 2 L)
  have hnormalL : ((twoCoreAmbient L).subgroupOf L).Normal := by
    rw [← Subgroup.comap_subtype, twoCoreAmbient,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  have hLnormalizer : L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCoreLL).mp hnormalL
  have hnormalP : ((twoCoreAmbient L).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCoreLP).mpr
      (hPL.trans hLnormalizer)
  have hpAmbient : IsPGroup 2 (twoCoreAmbient L) :=
    (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  have hpP : IsPGroup 2 ((twoCoreAmbient L).subgroupOf P) :=
    hpAmbient.of_equiv (Subgroup.subgroupOfEquivOfLe hCoreLP).symm
  have hleCoreP : (twoCoreAmbient L).subgroupOf P ≤ pCore 2 P :=
    le_sSup ⟨hnormalP, hpP⟩
  calc
    twoCoreAmbient L = ((twoCoreAmbient L).subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hCoreLP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hleCoreP
    _ = twoCoreAmbient P := rfl

omit [Finite G] in
private theorem mem_LSet_of_pSet_of_core_ne
    (S : Sylow 2 G) (M P : Subgroup G)
    (hP : P ∈ SectionThree.PSet M (S : Subgroup G))
    (hcoreM : twoCoreAmbient M ≠ ⊥) :
    M ∈ SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ P :=
    sylow_le_of_isSylowSubgroupIn hP.1.2.1
  have hSM : (S : Subgroup G) ≤ M := hSP.trans hP.1.1
  have hSylowM : IsSylowSubgroupIn (S : Subgroup G) M :=
    isSylowSubgroupIn_of_sylow_le S M hSM
  refine ⟨le_top, hSylowM, hcoreM, ?_⟩
  intro hScoreM
  apply hP.1.2.2.2
  apply le_antisymm
  · exact hScoreM.le.trans
      (twoCoreAmbient_le_of_le_of_common_sylow M P (S : Subgroup G)
        hP.1.1 hSylowM hP.1.2.1)
  · exact twoCoreAmbient_le_sylowImage hP.1.2.1

omit [Finite G] in
private theorem pstar_top_of_pstar_maxL
    {S L P : Subgroup G}
    (hL : L ∈ SectionThree.maxLSet (⊤ : Subgroup G) S)
    (hP : P ∈ SectionThree.PStarSet L S) :
    P ∈ SectionThree.PStarSet (⊤ : Subgroup G) S := by
  rcases hP.2 with ⟨M, hMmax, hsub⟩
  have hLlocal : L ∈ SectionThree.LSet L S :=
    ⟨le_rfl, hL.1.2.1, hL.1.2.2.1, hL.1.2.2.2⟩
  have hLM : L = M := hMmax.2 L hLlocal hMmax.1.1
  rw [← hLM] at hsub
  exact ⟨pSet_top_of_pSet hP.1, L, hL, hsub⟩

omit [Finite G] in
private theorem zSubgroup_le_centerAmbient (S : Sylow 2 G) :
    zSubgroup S ≤ (Subgroup.center S).map (S : Subgroup G).subtype := by
  unfold zSubgroup omegaOneCenterAmbient
  exact Subgroup.map_mono
    (Subgroup.map_subtype_le
      ((omega₁ (G := Subgroup.center S) (p := 2)) :
        Subgroup (Subgroup.center S)))

private theorem zSubgroup_ne_bot
    (S : Sylow 2 G) (heven : Even (Nat.card G)) :
    zSubgroup S ≠ ⊥ := by
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card heven.two_dvd
  let : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    S.isPGroup'.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map
      (Subgroup.center S).subtype)
    (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective).mp
  simpa [zSubgroup, omegaOneCenterAmbient] using hz

/-- The centralizer `C = C_G(Ω₁(Z(S)))` has nontrivial 2-core when `G`
has even order.  This is the nontriviality input for the `C`-family in (4.3)
and the comparison in (4.5). -/
public theorem twoCore_cSubgroup_ne_bot
    (S : Sylow 2 G) (heven : Even (Nat.card G)) :
    twoCoreAmbient (cSubgroup S) ≠ ⊥ := by
  let Z : Subgroup G := zSubgroup S
  let C : Subgroup G := cSubgroup S
  have hZS : Z ≤ (S : Subgroup G) :=
    (zSubgroup_le_centerAmbient S).trans
      (Subgroup.map_subtype_le (Subgroup.center S))
  have hZ2 : IsPGroup 2 Z := S.isPGroup'.to_le hZS
  have hZcomm : IsMulCommutative Z := by
    refine ⟨⟨fun a b ↦ ?_⟩⟩
    apply Subtype.ext
    obtain ⟨aS, haS, ha⟩ := zSubgroup_le_centerAmbient S a.property
    obtain ⟨bS, hbS, hb⟩ := zSubgroup_le_centerAmbient S b.property
    have hcomm := (Subgroup.mem_center_iff.mp haS) bS
    change (a : G) * (b : G) = (b : G) * (a : G)
    rw [← ha, ← hb]
    simpa using congrArg (fun x : S ↦ (x : G)) hcomm.symm
  have hZC : Z ≤ C := by
    change Z ≤ Subgroup.centralizer (Z : Set G)
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hZcomm
  have hZnormalC : (Z.subgroupOf C).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr
    change Subgroup.centralizer (Z : Set G) ≤
      Subgroup.normalizer (Z : Set G)
    exact Subgroup.centralizer_le_normalizer (Z : Set G)
  have hZ2C : IsPGroup 2 (Z.subgroupOf C) :=
    hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZC).symm
  have hZintCore : Z.subgroupOf C ≤ pCore 2 C :=
    le_sSup ⟨hZnormalC, hZ2C⟩
  have hZCore : Z ≤ twoCoreAmbient C := by
    calc
      Z = (Z.subgroupOf C).map C.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hZC).symm
      _ ≤ (pCore 2 C).map C.subtype := Subgroup.map_mono hZintCore
      _ = twoCoreAmbient C := rfl
  intro hcoreBot
  exact zSubgroup_ne_bot S heven
    (le_antisymm (hZCore.trans_eq hcoreBot) bot_le)

private theorem restricted_core_inf_eq
    (S : Sylow 2 G) (h : Hypotheses G S)
    (M : Subgroup G) (hcoreM : twoCoreAmbient M ≠ ⊥) :
    dSubgroup S =
      sInf {D : Subgroup G |
        ∃ P : Subgroup G,
          P ∈ SectionThree.PStarSet M (S : Subgroup G) ∪
            (SectionThree.PStarSet (⊤ : Subgroup G) (S : Subgroup G) \
              SectionThree.PSet M (S : Subgroup G)) ∧
          D = twoCoreAmbient P} := by
  classical
  let Sint : Subgroup G := (S : Subgroup G)
  let Fam : Set (Subgroup G) :=
    SectionThree.PStarSet M Sint ∪
      (SectionThree.PStarSet (⊤ : Subgroup G) Sint \
        SectionThree.PSet M Sint)
  let E : Subgroup G :=
    sInf {D : Subgroup G | ∃ P : Subgroup G, P ∈ Fam ∧
      D = twoCoreAmbient P}
  change dSubgroup S = E
  have h41 := lemma_four_one S h
  have hFamPSet : Fam ⊆ SectionThree.PSet (⊤ : Subgroup G) Sint := by
    intro P hP
    rcases hP with hP | hP
    · exact pSet_top_of_pSet hP.1
    · exact hP.1.1
  have hdE : dSubgroup S ≤ E := by
    rw [dSubgroup]
    apply le_sInf
    intro D hD
    obtain ⟨P, hP, rfl⟩ := hD
    apply sInf_le
    exact ⟨P, hFamPSet hP, rfl⟩
  have hLnonempty :
      (SectionThree.LSet (⊤ : Subgroup G) Sint).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h41.part_a.1
  obtain ⟨L₀, hL₀⟩ := hLnonempty
  have hdMax := (lemma_four_two S h L₀ hL₀).2.2
  have hEd : E ≤ dSubgroup S := by
    rw [hdMax]
    apply le_sInf
    intro D hD
    obtain ⟨L, hLmax, rfl⟩ := hD
    have hlocal := lemma_four_two S h L hLmax.1
    rw [← hlocal.2.1, hlocal.1, localDStar]
    apply le_sInf
    intro D hD
    obtain ⟨P, hPstarL, rfl⟩ := hD
    by_cases hPM : P ∈ SectionThree.PSet M Sint
    · have hML : M ∈ SectionThree.LSet (⊤ : Subgroup G) Sint :=
        mem_LSet_of_pSet_of_core_ne S M P hPM hcoreM
      have hlocalM := lemma_four_two S h M hML
      have hEStarM : E ≤ localDStar M Sint := by
        rw [localDStar]
        apply le_sInf
        intro D hD
        obtain ⟨Q, hQ, rfl⟩ := hD
        apply sInf_le
        exact ⟨Q, Or.inl hQ, rfl⟩
      have hlocalDCoreP : localD M Sint ≤ twoCoreAmbient P := by
        rw [localD]
        exact sInf_le ⟨P, hPM, rfl⟩
      exact hEStarM.trans ((le_of_eq hlocalM.1.symm).trans hlocalDCoreP)
    · have hPtop : P ∈ SectionThree.PStarSet (⊤ : Subgroup G) Sint :=
        pstar_top_of_pstar_maxL hLmax hPstarL
      apply sInf_le
      exact ⟨P, Or.inr ⟨hPtop, hPM⟩, rfl⟩
  exact le_antisymm hdE hEd

public theorem lemma_four_three
    (S : Sylow 2 G) (h : Hypotheses G S) :
    dSubgroup S =
        sInf {D₀ : Subgroup G |
          ∃ P : Subgroup G, P ∈ pZero S ∧ D₀ = twoCoreAmbient P} ∧
      dSubgroup S =
        sInf {D₁ : Subgroup G |
          ∃ P : Subgroup G, P ∈ pOne S ∧ D₁ = twoCoreAmbient P} := by
  have h41 := lemma_four_one S h
  constructor
  · simpa [pZero] using
      restricted_core_inf_eq S h (cSubgroup S)
        (twoCore_cSubgroup_ne_bot S h.even_order)
  · simpa [pOne] using
      restricted_core_inf_eq S h (mSubgroup S) h41.part_b

end Stellmacher.SectionFour
