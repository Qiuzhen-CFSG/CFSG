module

public import Submission.FeitThompson.PFsection8.Basic
import Submission.FeitThompson.PFsection8.PFsection8_11
import Submission.FeitThompson.PFsection8.PFsection8_9
import Submission.FeitThompson.PFsection8.SourceTypePBridge

noncomputable section

namespace Section8

universe v
universe w
universe u

@[expose] public def theorem_8_17_statement
    {G : Type u} [Group G] [Finite G]
    (Ms : List (Subgroup G))
    (MF Msigma : Subgroup G → Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G)
    (R : Subgroup G → G → Subgroup G) : Prop := by
  exact
    ∀ hG : IsMinCE G,
      letI : IsMinCE G := hG
      theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R →
        section16ListDisjointUnion
          (Ms.map fun M => subgroupPrimeSet (Msigma M))
          (subgroupPrimeSet (⊤ : Subgroup G)) ∧
        (∀ M : Subgroup G, M ∈ Ms →
          Nat.card (tildeA1 M) =
            (Nat.card (Msigma M) - 1) * M.index) ∧
        ((∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
          ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) →
          section16ListDisjointUnion
            (Ms.map fun M => tildeA1 M)
            (section16NonidentityElements (Set.univ : Set G))) ∧
        (∀ W W1 W2 S T SF TF : Subgroup G,
          theorem_8_8_source_case_b_data W W1 W2 S T SF TF →
            section16ListDisjointUnion
              ((Ms.map fun M => tildeA1 M) ++
                [section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ])
              (section16NonidentityElements (Set.univ : Set G)))

/-- Peterfalvi `(8.18)`. -/


private theorem theorem_8_17_subgroupPrimeSet_section10Msigma_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    subgroupPrimeSet (section10Msigma M) = section10SigmaPrimes M := by
  classical
  ext p
  constructor
  · intro hp
    exact (section10_msigma_isHall (G := G) hM).p_in_pi_of_p_dvd_card p (by
      simpa [subgroupPrimeSet] using hp)
  · intro hpσ
    have hpMset : p ∈ subgroupPrimeSet M := by
      exact (show p ∈ subgroupPrimeSet M ∧
        ∃ P : Sylow p.val M,
          Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M from by
          simpa [section10SigmaPrimes] using hpσ).1
    have hpM : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpMset
    have hKHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      section10_msigmaSubgroup_isHall (G := G) hM
    have hprod :
        p.val ∣ (section10MsigmaSubgroup M).index *
          Nat.card (section10MsigmaSubgroup M) := by
      simpa [Subgroup.index_mul_card (H := section10MsigmaSubgroup M)] using hpM
    rcases p.property.dvd_or_dvd hprod with hpidx | hpcard
    · exact False.elim ((hKHall.p_in_pi_of_p_dvd_index p hpidx) hpσ)
    · have hcard_eq : Nat.card (section10Msigma M) =
          Nat.card (section10MsigmaSubgroup M) := by
        simpa [section10Msigma] using
          (Subgroup.card_map_of_injective
            (K := section10MsigmaSubgroup M) (f := M.subtype) M.subtype_injective)
      exact by
        simpa [subgroupPrimeSet, hcard_eq] using hpcard

/-- In PF `(8.10)` source notation, the prime support of `M_s` is the BG
`sigma(M)` prime set. -/
public theorem theorem_8_17_subgroupPrimeSet_msigma_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1) :
    subgroupPrimeSet Ms = section10SigmaPrimes M := by
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hCases⟩
  rw [theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs]
  exact theorem_8_17_subgroupPrimeSet_section10Msigma_eq (G := G) hM

private theorem theorem_8_17_sigmaPrimes_disjointUnion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R) :
    section16ListDisjointUnion
      (Ms.map fun M => subgroupPrimeSet (Msigma M))
      (subgroupPrimeSet (⊤ : Subgroup G)) := by
  rcases hData with ⟨hReps, hEach⟩
  have hmap :
      (Ms.map fun M => subgroupPrimeSet (Msigma M)) =
        Ms.map section10SigmaPrimes := by
    apply List.map_congr_left
    intro M hMmem
    exact theorem_8_17_subgroupPrimeSet_msigma_eq (G := G) (hEach M hMmem).1
  rw [hmap]
  exact theorem_16_E_2 (G := G) Ms hReps

private theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_sourceR
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 = section16ConjugatesOfSetBySet (section16TildeM M R) Set.univ := by
  classical
  rcases hRep with ⟨h10, h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, _htildeA, _htildeA0, htildeA1⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  ext y
  constructor
  · intro hy
    rw [htildeA1] at hy
    rcases hy with ⟨a, haA1, x, hxLeft, g, hg, rfl⟩
    rcases hxLeft with ⟨r, hr, rfl⟩
    have haMs_ne : a ∈ Ms ∧ a ≠ 1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using haA1
    have haSigma : a ∈ section10Msigma M := by
      simpa [hMs_eq] using haMs_ne.1
    refine ⟨a * r, ?_, g, hg, rfl⟩
    exact ⟨a, haSigma, haMs_ne.2, r, hr, rfl⟩
  · intro hy
    rcases hy with ⟨x, hxTilde, g, hg, rfl⟩
    rcases hxTilde with ⟨a, haSigma, hane, r, hr, rfl⟩
    rw [htildeA1]
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haA1, a * r, ?_, g, hg, rfl⟩
    exact ⟨r, hr, rfl⟩

private theorem theorem_8_17_representativeR_eq_section14R_on_A1
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    ∀ a : G, a ∈ A1 → R a = section14R a := by
  classical
  rcases hRep with ⟨h10, h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  rcases h14 with
    ⟨hA1A, hAA0, hD, hRbot, hUnique, hReq, _htildeA, _htildeA0, _htildeA1⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  intro a haA1
  have haMs_ne : a ∈ Ms ∧ a ≠ 1 := by
    simpa [hA1, a1Set, section16NonidentityElements] using haA1
  have haSigma : a ∈ section10Msigma M := by
    simpa [hMs_eq] using haMs_ne.1
  have haA0 : a ∈ A0 := hAA0 (hA1A haA1)
  by_cases hCGM : Subgroup.centralizer ({a} : Set G) ≤ M
  · have haA0diff : a ∈ A0 \ D := by
      refine ⟨haA0, ?_⟩
      intro haD
      have haD' : a ∈ section8DSet M A0 := by
        simpa [hD] using haD
      exact haD'.2 hCGM
    have hRbot_a : R a = (⊥ : Subgroup G) := hRbot a haA0diff
    have h14bot : section14R a = (⊥ : Subgroup G) :=
      section16_section14R_eq_bot_of_centralizer_le_public
        (G := G) hM haSigma haMs_ne.2 hCGM
    exact hRbot_a.trans h14bot.symm
  · have haD : a ∈ D := by
      rw [hD]
      exact ⟨haA0, hCGM⟩
    rcases hUnique a haD with ⟨L, hLmem, hLuniq⟩
    have hNpack :=
      section16_section14N_data_of_not_centralizer_le
        (G := G) hM haSigma haMs_ne.2 hCGM
    have hN_eq_L : section14N a = L := hLuniq (section14N a) hNpack.1
    have hSet :
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)) = {L} := by
      ext N
      constructor
      · intro hNmem
        have hNL : N = L := hLuniq N hNmem
        simp [hNL]
      · intro hNmem
        have hNL : N = L := by
          simpa using hNmem
        simpa [hNL] using hLmem
    have hLF : section16MFSubgroup L (section10Msigma L) := by
      simpa [hN_eq_L] using hNpack.2.2
    have hR_eq : R a = elementCentralizerIn (section10Msigma L) a :=
      hReq a haD L (section10Msigma L) hSet hLF
    have h14_eq : section14R a = elementCentralizerIn (section10Msigma L) a := by
      simpa [hN_eq_L] using hNpack.2.1
    exact hR_eq.trans h14_eq.symm

private theorem theorem_8_17_tildeM_representativeR_eq_section14R
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R)
    (hR : ∀ a : G, a ∈ A1 → R a = section14R a) :
    section16TildeM M R =
      section16TildeM M (fun x : G => section14R x) := by
  classical
  rcases hRep with ⟨h10, _h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  ext y
  constructor
  · intro hy
    rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haSigma, hane, r, ?_, rfl⟩
    simpa [hR a haA1] using hr
  · intro hy
    rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haSigma, hane, r, ?_, rfl⟩
    simpa [hR a haA1] using hr

private theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 =
      section16ConjugatesOfSetBySet
        (section16TildeM M (fun x : G => section14R x)) Set.univ := by
  have hR : ∀ a : G, a ∈ A1 → R a = section14R a :=
    theorem_8_17_representativeR_eq_section14R_on_A1 (G := G) hRep
  calc
    tildeA1 = section16ConjugatesOfSetBySet (section16TildeM M R) Set.univ := by
      exact theorem_8_17_tildeA1_eq_conjugates_tildeM_sourceR (G := G) hRep
    _ = section16ConjugatesOfSetBySet
          (section16TildeM M (fun x : G => section14R x)) Set.univ := by
      rw [theorem_8_17_tildeM_representativeR_eq_section14R (G := G) hRep hR]

public theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 =
      section16ConjugatesOfSetBySet
        (section16TildeM M (fun x : G => section14R x)) Set.univ :=
  theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R (G := G) hRep

private theorem theorem_8_17_tildeA1_bg_map_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R) :
    (Ms.map fun M => tildeA1 M) =
      Ms.map fun M =>
        section16ConjugatesOfSetBySet
          (section16TildeM M (fun x : G => section14R x)) Set.univ := by
  rcases hData with ⟨_hReps, hEach⟩
  apply List.map_congr_left
  intro M hMmem
  exact theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R (G := G)
    (hEach M hMmem)

private theorem theorem_8_17_tildeA1_disjointUnion_tildeG
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R) :
    section16ListDisjointUnion
      (Ms.map fun M => tildeA1 M)
      (section16TildeGForRepresentatives Ms (fun _ x => section14R x)) := by
  rcases hData with ⟨hReps, hEach⟩
  have hData' : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R :=
    ⟨hReps, hEach⟩
  rw [theorem_8_17_tildeA1_bg_map_eq (G := G) hData']
  exact theorem_16_E_3_tilde_disjointUnion (G := G) Ms hReps

private theorem theorem_8_17_tildeA1_card_eq_of_representativeR_eq_section14R
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R)
    (hR : ∀ a : G, a ∈ A1 → R a = section14R a) :
    Nat.card tildeA1 = (Nat.card Ms - 1) * M.index := by
  classical
  rcases hRep with ⟨h10, h14⟩
  have hRep' : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R :=
    ⟨h10, h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  have hTildeM_eq :
      section16TildeM M R =
        section16TildeM M (fun x : G => section14R x) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
      have haMs : a ∈ Ms := by
        simpa [hMs_eq] using haSigma
      have haA1 : a ∈ A1 := by
        simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
      refine ⟨a, haSigma, hane, r, ?_, rfl⟩
      simpa [hR a haA1] using hr
    · intro hy
      rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
      have haMs : a ∈ Ms := by
        simpa [hMs_eq] using haSigma
      have haA1 : a ∈ A1 := by
        simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
      refine ⟨a, haSigma, hane, r, ?_, rfl⟩
      simpa [hR a haA1] using hr
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  calc
    Nat.card tildeA1 =
        Nat.card (section16ConjugatesOfSetBySet (section16TildeM M R) Set.univ) := by
      rw [theorem_8_17_tildeA1_eq_conjugates_tildeM_sourceR (G := G) hRep']
    _ = Nat.card (section16ConjugatesOfSetBySet
          (section16TildeM M (fun x : G => section14R x)) Set.univ) := by
      rw [hTildeM_eq]
    _ = (Nat.card (section10Msigma M) - 1) * M.index :=
      theorem_16_E_1 (G := G) hM hMF hKU
    _ = (Nat.card Ms - 1) * M.index := by
      rw [hMs_eq]

private theorem theorem_8_17_tildeA1_card_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    Nat.card tildeA1 = (Nat.card Ms - 1) * M.index :=
  theorem_8_17_tildeA1_card_eq_of_representativeR_eq_section14R (G := G) hRep
    (theorem_8_17_representativeR_eq_section14R_on_A1 (G := G) hRep)

/-- The proved PF `(8.17)(a,b)` conclusions, separated from the remaining
cover-alternative debt in `(8.17)(c)`. -/
public theorem theorem_8_17_prime_and_card_conclusions
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R) :
    section16ListDisjointUnion
        (Ms.map fun M => subgroupPrimeSet (Msigma M))
        (subgroupPrimeSet (⊤ : Subgroup G)) ∧
      ∀ M : Subgroup G, M ∈ Ms →
        Nat.card (tildeA1 M) =
          (Nat.card (Msigma M) - 1) * M.index := by
  refine ⟨theorem_8_17_sigmaPrimes_disjointUnion (G := G) hData, ?_⟩
  rcases hData with ⟨_hReps, hEach⟩
  intro M hMmem
  exact theorem_8_17_tildeA1_card_eq (G := G) (hEach M hMmem)

private theorem theorem_8_17_tildeA1_disjointUnion_nonidentity_of_noMaximalTypeP
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hNoP : ∀ H : Subgroup G, ¬ section16MaximalTypeP H) :
    section16ListDisjointUnion
      (Ms.map fun M => tildeA1 M)
      (section16NonidentityElements (Set.univ : Set G)) := by
  rcases hData with ⟨hReps, hEach⟩
  have hData' :
      theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R :=
    ⟨hReps, hEach⟩
  have hCover :
      section16NonidentityElements (Set.univ : Set G) =
        section16TildeGForRepresentatives Ms (fun _ x => section14R x) :=
    theorem_16_E_3_noP_nonidentity_eq_tildeG (G := G) Ms hReps hNoP
  rw [hCover]
  exact theorem_8_17_tildeA1_disjointUnion_tildeG (G := G) hData'

private theorem theorem_8_17_noMaximalTypeP_of_all_source_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (hAll :
      ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF)
    (hSourceTypeI_to_BG :
      ∀ {M MF : Subgroup G}, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF → typeIDefinitionData M MF →
          section16TypeI M MF) :
    ∀ H : Subgroup G, ¬ section16MaximalTypeP H := by
  intro H hHP
  have hHmax : H ∈ section9MaximalSubgroups G := by
    rcases (by simpa [section16MaximalTypeP, section14MFamilyP] using hHP) with
      ⟨hHmax, _hKappa⟩
    exact hHmax
  rcases hAll H hHmax with ⟨HF, hHF, hSrcI⟩
  exact (section16_not_typeI_of_maximalTypeP (G := G) hHP hHF)
    (hSourceTypeI_to_BG hHmax hHF hSrcI)

private theorem theorem_8_17_mfSubgroup_eq
    {G : Type u} [Group G] [Finite G]
    {M MF NF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hNF : section16MFSubgroup M NF) :
    MF = NF :=
  le_antisymm (hNF.2 MF hMF.1) (hMF.2 NF hNF.1)

private theorem theorem_8_17_bg_typeI_of_source_choice
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms)
    (hSrcI : typeIDefinitionData M MF) :
    section16TypeI M MF := by
  classical
  have hNot :
      ¬ typeIIDefinitionData M MF ∧
        ¬ typeIIIDefinitionData M MF ∧
        ¬ typeIVDefinitionData M MF ∧
        ¬ typeVDefinitionData M MF := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · rcases hI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      exact ⟨hnotII, hnotIII, hnotIV, hnotV⟩
    · exact False.elim (hII.1 hSrcI)
    · exact False.elim (hIII.1 hSrcI)
    · exact False.elim (hIV.1 hSrcI)
    · exact False.elim (hV.1 hSrcI)
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact hTypeI
  · exact False.elim
      (hNot.1 (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
  · exact False.elim
      (hNot.2.1 (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
  · exact False.elim
      (hNot.2.2.1 (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
  · exact False.elim
      (hNot.2.2.2 (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))

private theorem theorem_8_17_representative_bg_typeI_of_all_source_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R)
    (hAllM : ∃ NF : Subgroup G, section16MFSubgroup M NF ∧
      typeIDefinitionData M NF) :
    section16TypeI M MF := by
  rcases hRep with ⟨h10, _h14⟩
  rcases h10 with ⟨hM, hMF, hMs, _hA1, _hCases⟩
  rcases hAllM with ⟨NF, hNF, hSrcI⟩
  have hNF_eq : NF = MF := theorem_8_17_mfSubgroup_eq hNF hMF
  subst NF
  exact theorem_8_17_bg_typeI_of_source_choice (G := G) hM hMF hMs hSrcI

private theorem theorem_8_17_noMaximalTypeP_of_all_source_typeI_representatives
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hAll :
      ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) :
    ∀ H : Subgroup G, ¬ section16MaximalTypeP H := by
  classical
  rcases hData with ⟨hReps, hEach⟩
  intro H hHP
  have hHmax : H ∈ section9MaximalSubgroups G := by
    rcases (by simpa [section16MaximalTypeP, section14MFamilyP] using hHP) with
      ⟨hHmax, _hKappa⟩
    exact hHmax
  rcases hReps.2.2 H hHmax with ⟨M, hMpack, _hUnique⟩
  rcases hMpack with ⟨hMmem, g, hH_eq⟩
  have hRep := hEach M hMmem
  rcases hRep with ⟨h10, h14⟩
  rcases h10 with ⟨hMmax, hMF, _hMs, _hA1, _hCases⟩
  have hTypeI :
      section16TypeI M (MF M) :=
    theorem_8_17_representative_bg_typeI_of_all_source_typeI
      (G := G) (M := M) (MF := MF M) (Ms := Msigma M)
      (A := A M) (A0 := A0 M) (A1 := A1 M) (D := D M)
      (tildeA := tildeA M) (tildeA0 := tildeA0 M)
      (tildeA1 := tildeA1 M) (R := R M) ⟨⟨hMmax, hMF, _hMs, _hA1, _hCases⟩, h14⟩
      (hAll M hMmax)
  have hHmemP : H ∈ section14MFamilyP G := by
    simpa [section16MaximalTypeP] using hHP
  have hMmemP : M ∈ section14MFamilyP G := by
    have hBack : H.conjBy g⁻¹ ∈ section14MFamilyP G :=
      section14_mFamilyP_conjBy (G := G) (M := H) g⁻¹ hHmemP
    simpa [hH_eq, Subgroup.conjBy_inv] using hBack
  have hMP : section16MaximalTypeP M := by
    simpa [section16MaximalTypeP] using hMmemP
  exact (section16_not_typeI_of_maximalTypeP (G := G) hMP hMF) hTypeI

private theorem theorem_8_17_all_source_typeI_disjointUnion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hAll :
      ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) :
    section16ListDisjointUnion
      (Ms.map fun M => tildeA1 M)
      (section16NonidentityElements (Set.univ : Set G)) :=
  theorem_8_17_tildeA1_disjointUnion_nonidentity_of_noMaximalTypeP (G := G) hData
    (theorem_8_17_noMaximalTypeP_of_all_source_typeI_representatives
      (G := G) hData hAll)

private theorem theorem_8_17_all_source_typeI_disjointUnion_of_typeI_to_BG
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hAll :
      ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF)
    (hSourceTypeI_to_BG :
      ∀ {M MF : Subgroup G}, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF → typeIDefinitionData M MF →
          section16TypeI M MF) :
    section16ListDisjointUnion
      (Ms.map fun M => tildeA1 M)
      (section16NonidentityElements (Set.univ : Set G)) :=
  theorem_8_17_tildeA1_disjointUnion_nonidentity_of_noMaximalTypeP (G := G) hData
    (theorem_8_17_noMaximalTypeP_of_all_source_typeI
      (G := G) hAll hSourceTypeI_to_BG)

private theorem theorem_8_17_listDisjointUnion_append_single_of_left
    {α : Type*} {sets : List (Set α)} {T Z U : Set α}
    (hsets : section16ListDisjointUnion sets T)
    (hTZ : section16ListDisjointUnion [T, Z] U) :
    section16ListDisjointUnion (sets ++ [Z]) U := by
  classical
  rcases hsets with ⟨hcoverSets, hdisSets⟩
  rcases hTZ with ⟨hcoverTZ, hdisTZ⟩
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hxU
      rcases (hcoverTZ x).1 hxU with ⟨i, hxi⟩
      fin_cases i
      · have hxT : x ∈ T := by simpa using hxi
        rcases (hcoverSets x).1 hxT with ⟨j, hxj⟩
        let j' : Fin (sets ++ [Z]).length := ⟨j.1, by simp⟩
        refine ⟨j', ?_⟩
        have hget : (sets ++ [Z]).get j' = sets.get j := by
          simp [j', List.get_eq_getElem]
        rw [hget]
        exact hxj
      · refine ⟨⟨sets.length, by simp⟩, ?_⟩
        simpa using hxi
    · rintro ⟨i, hxi⟩
      by_cases hi : i.1 < sets.length
      · let j : Fin sets.length := ⟨i.1, hi⟩
        have hget : (sets ++ [Z]).get i = sets.get j := by
          simp [j, List.get_eq_getElem, hi]
        rw [hget] at hxi
        have hxT : x ∈ T := (hcoverSets x).2 ⟨j, hxi⟩
        exact (hcoverTZ x).2 ⟨⟨0, by simp⟩, by simpa using hxT⟩
      · have hget : (sets ++ [Z]).get i = Z := by
          have hival : i.1 = sets.length := by
            have hlt : i.1 < sets.length + 1 := by simpa using i.2
            omega
          simp [List.get_eq_getElem, hival]
        rw [hget] at hxi
        exact (hcoverTZ x).2 ⟨⟨1, by simp⟩, by simpa using hxi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    by_cases hi : i.1 < sets.length
    · let ii : Fin sets.length := ⟨i.1, hi⟩
      have hgeti : (sets ++ [Z]).get i = sets.get ii := by
        simp [ii, List.get_eq_getElem, hi]
      rw [hgeti] at hxi
      by_cases hj : j.1 < sets.length
      · let jj : Fin sets.length := ⟨j.1, hj⟩
        have hgetj : (sets ++ [Z]).get j = sets.get jj := by
          simp [jj, List.get_eq_getElem, hj]
        rw [hgetj] at hxj
        have hijj : ii ≠ jj := by
          intro h
          apply hij
          apply Fin.ext
          simpa [ii, jj] using congrArg Fin.val h
        exact (Set.disjoint_left.mp (hdisSets ii jj hijj)) hxi hxj
      · have hgetj : (sets ++ [Z]).get j = Z := by
          have hjval : j.1 = sets.length := by
            have hlt : j.1 < sets.length + 1 := by simpa using j.2
            omega
          simp [List.get_eq_getElem, hjval]
        rw [hgetj] at hxj
        have hxT : x ∈ T := (hcoverSets x).2 ⟨ii, hxi⟩
        have h01 : (⟨0, by simp⟩ : Fin [T, Z].length) ≠ ⟨1, by simp⟩ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        have hdisTZ' : Disjoint T Z := by
          simpa using hdisTZ ⟨0, by simp⟩ ⟨1, by simp⟩ h01
        exact (Set.disjoint_left.mp hdisTZ') hxT hxj
    · have hgeti : (sets ++ [Z]).get i = Z := by
        have hival : i.1 = sets.length := by
          have hlt : i.1 < sets.length + 1 := by simpa using i.2
          omega
        simp [List.get_eq_getElem, hival]
      rw [hgeti] at hxi
      by_cases hj : j.1 < sets.length
      · let jj : Fin sets.length := ⟨j.1, hj⟩
        have hgetj : (sets ++ [Z]).get j = sets.get jj := by
          simp [jj, List.get_eq_getElem, hj]
        rw [hgetj] at hxj
        have hxT : x ∈ T := (hcoverSets x).2 ⟨jj, hxj⟩
        have h10 : (⟨1, by simp⟩ : Fin [T, Z].length) ≠ ⟨0, by simp⟩ := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        have hdisZT' : Disjoint Z T := by
          simpa using hdisTZ ⟨1, by simp⟩ ⟨0, by simp⟩ h10
        exact (Set.disjoint_left.mp hdisZT') hxi hxT
      · have hival : i.1 = sets.length := by
          have hlt : i.1 < sets.length + 1 := by simpa using i.2
          omega
        have hjval : j.1 = sets.length := by
          have hlt : j.1 < sets.length + 1 := by simpa using j.2
          omega
        exfalso
        apply hij
        apply Fin.ext
        simp [hival, hjval]

private theorem theorem_8_17_source_case_b_exists_KUData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    ∃ U : Subgroup G, section16KUData S W1 U := by
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  rcases sourceTypeP_exists_typePDefinitionData_of_source_late_type
      (G := G) (M := S) (MF := SF) _hSType with
    ⟨U, W1S, W2S, hP⟩
  have hcompW1 : section12ComplementIn S (ambientDerivedSubgroup S) W1 := by
    refine ⟨section12_ambientDerivedSubgroup_le, ?_, _hSeq, _hSdisj⟩
    rw [_hSeq]
    exact le_sup_right
  exact sourceTypeP_exists_KUData_of_complement
    (G := G) (M := S) (MF := SF) (U := U) (W1 := W1S) (W2 := W2S)
    (K := W1) hSmax hP hcompW1

private theorem theorem_8_17_source_case_b_Kstar_eq_of_KUData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {W W1 W2 S T SF TF U : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF)
    (hKU : section16KUData S W1 U) :
    section16Kstar S W1 = W2 := by
  have hcase0 : theorem_8_8_source_case_b_data W W1 W2 S T SF TF := hcase
  rcases hcase with
    ⟨_hprod, _hcyc, hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  rcases section16_exists_typeCommon_of_K_ne_bot
      (G := G) hSmax hSF hKU hW1ne with
    ⟨V, hCommon⟩
  have hP : typePDefinitionData S SF V W1 (section16Kstar S W1) :=
    theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hSmax hSF hKU hCommon
  have hEq : W2 = section16Kstar S W1 :=
    (theorem_8_9 (G := G) W W1 W2 S T SF TF V (section16Kstar S W1))
      hcase0 hP
  exact hEq.symm

private theorem theorem_8_17_source_case_b_KUData_Kstar_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    ∃ U : Subgroup G, section16KUData S W1 U ∧ section16Kstar S W1 = W2 := by
  rcases theorem_8_17_source_case_b_exists_KUData (G := G)
      (W := W) (W1 := W1) (W2 := W2) (S := S) (T := T) (SF := SF) (TF := TF)
      hcase with
    ⟨U, hKU⟩
  exact ⟨U, hKU, theorem_8_17_source_case_b_Kstar_eq_of_KUData
    (G := G) (W := W) (W1 := W1) (W2 := W2) (S := S) (T := T)
    (SF := SF) (TF := TF) hcase hKU⟩

private theorem theorem_8_17_source_case_b_tildeG_hatW_disjointUnion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    (hReps : representativeSystemData Ms)
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    section16ListDisjointUnion
      [section16TildeGForRepresentatives Ms (fun _ x => section14R x),
        section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ]
      (section16NonidentityElements (Set.univ : Set G)) := by
  rcases hcase with
    ⟨_hprod, _hcyc, hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  rcases theorem_8_17_source_case_b_KUData_Kstar_eq (G := G)
      (W := W) (W1 := W1) (W2 := W2) (S := S) (T := T) (SF := SF) (TF := TF)
      (by
        exact ⟨_hprod, _hcyc, hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, hSF, _hTF,
          _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
          _hCover⟩) with
    ⟨U, hKU, hKstar⟩
  have hMP : section16MaximalTypeP S :=
    section16_maximalTypeP_of_KUData_ne_bot (G := G) hSmax hKU hW1ne
  have hHat :
      section16HatZ W1 (section16Kstar S W1) = section16HatW W1 W2 := by
    simp [section16HatZ, section16HatW, section16ZSubgroup, hKstar]
  have hCover :=
    (theorem_16_E_3 (G := G) (M := S) (MF := SF) (K := W1) (U := U)
      Ms hSmax hSF hKU hReps).2.2 ⟨S, hMP⟩ hMP
  simpa [hHat] using hCover

private theorem theorem_8_17_source_case_b_disjointUnion
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R)
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    section16ListDisjointUnion
      ((Ms.map fun M => tildeA1 M) ++
        [section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ])
      (section16NonidentityElements (Set.univ : Set G)) := by
  rcases hData with ⟨hReps, hEach⟩
  have hData' :
      theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R :=
    ⟨hReps, hEach⟩
  exact theorem_8_17_listDisjointUnion_append_single_of_left
    (theorem_8_17_tildeA1_disjointUnion_tildeG (G := G) hData')
    (theorem_8_17_source_case_b_tildeG_hatW_disjointUnion
      (G := G) (Ms := Ms) hReps hcase)

private theorem theorem_8_17_cover_alternatives
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF Msigma : Subgroup G → Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G}
    {R : Subgroup G → G → Subgroup G}
    (hData : theorem_8_17_source_data Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R) :
    ((∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) →
      section16ListDisjointUnion
        (Ms.map fun M => tildeA1 M)
        (section16NonidentityElements (Set.univ : Set G))) ∧
    (∀ W W1 W2 S T SF TF : Subgroup G,
      theorem_8_8_source_case_b_data W W1 W2 S T SF TF →
        section16ListDisjointUnion
          ((Ms.map fun M => tildeA1 M) ++
            [section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ])
          (section16NonidentityElements (Set.univ : Set G))) := by
  constructor
  · intro hAll
    exact theorem_8_17_all_source_typeI_disjointUnion (G := G) hData hAll
  · intro W W1 W2 S T SF TF hcase
    exact theorem_8_17_source_case_b_disjointUnion (G := G) hData hcase

public theorem theorem_8_17
    {G : Type u} [Group G] [Finite G]
    (Ms : List (Subgroup G))
    (MF Msigma : Subgroup G → Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Subgroup G → Set G)
    (R : Subgroup G → G → Subgroup G) :
    theorem_8_17_statement Ms MF Msigma A A0 A1 D tildeA tildeA0 tildeA1 R := by
  dsimp [theorem_8_17_statement]
  intro hG hData
  letI : IsMinCE G := hG
  have hPrimeCard :
      section16ListDisjointUnion
          (Ms.map fun M => subgroupPrimeSet (Msigma M))
          (subgroupPrimeSet (⊤ : Subgroup G)) ∧
        ∀ M : Subgroup G, M ∈ Ms →
          Nat.card (tildeA1 M) =
            (Nat.card (Msigma M) - 1) * M.index :=
    theorem_8_17_prime_and_card_conclusions (G := G) hData
  have hCover :
      ((∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) →
        section16ListDisjointUnion
          (Ms.map fun M => tildeA1 M)
          (section16NonidentityElements (Set.univ : Set G))) ∧
      (∀ W W1 W2 S T SF TF : Subgroup G,
        theorem_8_8_source_case_b_data W W1 W2 S T SF TF →
          section16ListDisjointUnion
            ((Ms.map fun M => tildeA1 M) ++
              [section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ])
            (section16NonidentityElements (Set.univ : Set G))) :=
    theorem_8_17_cover_alternatives (G := G) hData
  exact ⟨hPrimeCard.1, hPrimeCard.2, hCover.1, hCover.2⟩

end Section8
