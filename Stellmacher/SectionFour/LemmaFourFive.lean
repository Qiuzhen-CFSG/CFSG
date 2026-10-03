module

public import Stellmacher.SectionFour.LemmaFourFour
public import Theory.GroupTheory.PGroup.Subnormal

/-!
# Stellmacher's Lemma 4.5

Assume the global family `PSet ⊤ S` is covered by the two restricted
families attached to `M = mSubgroup S` and `C = cSubgroup S`.  A global
member outside the `M`-family has, by (4.4), a `Lambda`-partner in `pOne`.
Because the original member lies in `C`, triviality of the joined 2-core
forces that partner into `PStarSet M S`.

Under the additional containment `PStarSet C S ⊆ PSet M S`, Lemma 4.2
compares the two core intersections and gives `O₂(M) ≤ O₂(C)`.  For the
Sylow conclusion, (3.3)(a) shows that `O₂(O²(P*))` is Sylow in `O²(P*)`.
The residual is subnormal in `M`, so the standard subnormal-p-subgroup
theorem puts this 2-core inside `O₂(M)`.  A normal-product argument then
shows that `O₂(C)` is Sylow in `O²(P*) O₂(C)`.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (4.5),
journal page 25.
-/

open scoped Pointwise

namespace Stellmacher.SectionFour

open BenderSuzuki.External

universe u

private theorem twoResidualAmbient_eq_map_hktPResidual
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualAmbient P = (hktPResidual 2 P).map P.subtype := by
  have heq : twoResidualSubgroup P = hktPResidual 2 P := by
    apply le_antisymm
    · have hnormal : (hktPResidual 2 P).Normal := hktPResidual_normal
      let _ : (hktPResidual 2 P).Normal := hnormal
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
        (hktPResidual_quotient_isPGroup (Q := P) (q := 2))
      apply sInf_le
      refine ⟨hnormal, n, ?_⟩
      simpa [Subgroup.index_eq_card] using hn
    · apply le_sInf
      intro N hN
      have hnormal : N.Normal := hN.1
      let _ : N.Normal := hnormal
      obtain ⟨n, hn⟩ := hN.2
      apply hktPResidual_le N hnormal
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  simp [twoResidualAmbient, heq]

private theorem twoCoreAmbient_isSylow_twoResidualAmbient
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G)
    (hpquot : ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsPGroup p
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))) :
    IsSylowSubgroupIn (twoCoreAmbient (twoResidualAmbient P))
      (twoResidualAmbient P) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hp, hpodd, hpgroup⟩ := hpquot
  let _ : Fact p.Prime := ⟨hp⟩
  have hpne : 2 ≠ p := by
    intro heq
    subst p
    obtain ⟨k, hk⟩ := hpodd
    omega
  let A : Subgroup G := twoResidualAmbient P
  have hAP : A ≤ P := Subgroup.map_subtype_le (twoResidualSubgroup P)
  let iAP : A →* P := Subgroup.inclusion hAP
  let qP : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
  let f : A →* P ⧸ pCore 2 P := qP.comp iAP
  have hAsub : A.subgroupOf P = hktPResidual 2 P := by
    rw [show A = (hktPResidual 2 P).map P.subtype by
      simpa [A] using twoResidualAmbient_eq_map_hktPResidual P,
      subgroupOf_map_subtype_eq]
  have hfrange : f.range =
      twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)) := by
    calc
      f.range = (A.subgroupOf P).map qP := by
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          exact Subgroup.mem_map.mpr ⟨iAP a, a.property, rfl⟩
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
          refine ⟨⟨y, hy⟩, ?_⟩
          exact hyx
      _ = (hktPResidual 2 P).map qP := by rw [hAsub]
      _ = hktPResidual 2 (P ⧸ pCore 2 P) := by
        exact SectionThree.map_hktPResidual_quotient 2 (pCore 2 P)
      _ = twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)) :=
        SectionThree.twoResidualAmbient_top_eq_hktPResidual.symm
  let T : Sylow 2 A := Classical.choice (Sylow.nonempty (p := 2) (G := A))
  have hTmap2 : IsPGroup 2 ((T : Subgroup A).map f) := T.isPGroup'.map f
  have hTmapP : IsPGroup p ((T : Subgroup A).map f) := by
    apply hpgroup.to_le
    rw [← hfrange]
    exact Subgroup.map_le_range f (T : Subgroup A)
  have hTmapBot : (T : Subgroup A).map f = ⊥ := by
    apply disjoint_self.mp
    exact IsPGroup.disjoint_of_ne 2 p hpne _ _ hTmap2 hTmapP
  let K : Subgroup A := (pCore 2 P).comap iAP
  have hKnormal : K.Normal := (pCore_normal (p := 2) (G := P)).comap iAP
  have hKp : IsPGroup 2 K :=
    (pCore_isPGroup (p := 2) (G := P)).comap_of_injective iAP
      (Subgroup.inclusion_injective hAP)
  have hKcore : K ≤ pCore 2 A := le_sSup ⟨hKnormal, hKp⟩
  refine ⟨T, le_antisymm ?_ ?_⟩
  · intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨t, hKcore ?_, rfl⟩
    change iAP t ∈ pCore 2 P
    apply (QuotientGroup.eq_one_iff (N := pCore 2 P) (x := iAP t)).mp
    change f t = 1
    have htmap : f t ∈ (T : Subgroup A).map f :=
      Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    rw [hTmapBot] at htmap
    exact htmap
  · exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := A)).le_sylow_of_normal T)

private theorem isSylow_two_of_normal_product
    {G : Type u} [Group G] [Finite G]
    (P A Q : Subgroup G)
    (hAP : A ≤ P) (hQP : Q ≤ P)
    (hAnormalP : (A.subgroupOf P).Normal)
    (hASylow : IsSylowSubgroupIn (twoCoreAmbient A) A)
    (hcoreQ : twoCoreAmbient A ≤ Q)
    (hQ2 : IsPGroup 2 Q) :
    IsSylowSubgroupIn Q (A ⊔ Q) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup G := A ⊔ Q
  have hEP : E ≤ P := sup_le hAP hQP
  have hAE : A ≤ E := le_sup_left
  have hQE : Q ≤ E := le_sup_right
  have hAnormalE : (A.subgroupOf E).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAE]
    intro a e ha he
    exact (Subgroup.normal_subgroupOf_iff hAP).mp hAnormalP
      a e ha (hEP he)
  have hEnormalizer : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mp hAnormalE
  have hQnormalizer : Q ≤ Subgroup.normalizer (A : Set G) :=
    hQE.trans hEnormalizer
  let QE : Subgroup E := Q.subgroupOf E
  have hQE2 : IsPGroup 2 QE :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQE).symm
  obtain ⟨T, hQET⟩ := hQE2.exists_le_sylow
  obtain ⟨TA, hTAmap⟩ := hASylow
  have hTAeq : (TA : Subgroup A) = pCore 2 A := by
    apply Subgroup.map_injective A.subtype_injective
    simpa [twoCoreAmbient] using hTAmap
  have hpSubgroup_le_core (R : Subgroup A) (hR2 : IsPGroup 2 R) :
      R ≤ pCore 2 A := by
    obtain ⟨U, hRU⟩ := hR2.exists_le_sylow
    have hTAU : (TA : Subgroup A) ≤ (U : Subgroup A) := by
      rw [hTAeq]
      exact (pCore_isPGroup (p := 2) (G := A)).le_sylow_of_normal U
    have hUTA : (U : Subgroup A) = (TA : Subgroup A) :=
      TA.is_maximal' U.isPGroup' hTAU
    exact hRU.trans_eq (hUTA.trans hTAeq)
  have hTEQ : (T : Subgroup E) ≤ QE := by
    intro t ht
    have hEset : (E : Set G) = (A : Set G) * (Q : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left A Q hQnormalizer
    have htE : (t : G) ∈ (A : Set G) * (Q : Set G) := by
      rw [← hEset]
      exact t.property
    rcases htE with ⟨a, ha, q, hq, haq⟩
    let aE : E := ⟨a, hAE ha⟩
    let qE : E := ⟨q, hQE hq⟩
    have hqT : qE ∈ (T : Subgroup E) := hQET hq
    have haEeq : aE = t * qE⁻¹ := by
      apply E.subtype_injective
      change a = (t : G) * q⁻¹
      rw [← haq]
      simp
    have haT : aE ∈ (T : Subgroup E) := by
      rw [haEeq]
      exact T.mul_mem ht (T.inv_mem hqT)
    let iAE : A →* E := Subgroup.inclusion hAE
    let R : Subgroup A := (T : Subgroup E).comap iAE
    have hR2 : IsPGroup 2 R :=
      T.isPGroup'.comap_of_injective iAE (Subgroup.inclusion_injective hAE)
    have haCoreA : a ∈ twoCoreAmbient A := by
      change a ∈ (pCore 2 A).map A.subtype
      refine ⟨⟨a, ha⟩, hpSubgroup_le_core R hR2 ?_, rfl⟩
      exact haT
    have haQ : a ∈ Q := hcoreQ haCoreA
    change (t : G) ∈ Q
    rw [← haq]
    exact Q.mul_mem haQ hq
  refine ⟨T, ?_⟩
  have hTEQeq : (T : Subgroup E) = QE :=
    le_antisymm hTEQ hQET
  rw [hTEQeq]
  exact Subgroup.map_subgroupOf_eq_of_le hQE

private theorem sylow_le_of_isSylowSubgroupIn
    {G : Type u} [Group G] {S P : Subgroup G}
    (hSylow : IsSylowSubgroupIn S P) : S ≤ P := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_subtype_le (T : Subgroup P)

private theorem isSylowSubgroupIn_of_global_sylow_le
    {G : Type u} [Group G]
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) :
    IsSylowSubgroupIn (S : Subgroup G) H := by
  refine ⟨S.subtype hSH, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSH]

private theorem twoCoreAmbient_le_sylowImage
    {G : Type u} [Group G] [Finite G]
    {S P : Subgroup G} (hSylow : IsSylowSubgroupIn S P) :
    twoCoreAmbient P ≤ S := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)

private theorem twoCoreAmbient_normal_subgroupOf
    {G : Type u} [Group G] (H : Subgroup G) :
    ((twoCoreAmbient H).subgroupOf H).Normal := by
  change ((pCore 2 H).map H.subtype).comap H.subtype |>.Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

private theorem twoCoreAmbient_le_twoCoreAmbient_of_intermediate
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hKH : K ≤ H)
    (hcoreK : twoCoreAmbient H ≤ K) :
    twoCoreAmbient H ≤ twoCoreAmbient K := by
  have hnormalK : ((twoCoreAmbient H).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hcoreK]
    intro x k hx hk
    exact (Subgroup.normal_subgroupOf_iff
      (Subgroup.map_subtype_le (pCore 2 H))).mp
        (twoCoreAmbient_normal_subgroupOf H) x k hx (hKH hk)
  exact isPGroup_le_pCoreAmbient_of_isSubnormalIn K (twoCoreAmbient H) 2
    hcoreK hnormalK.isSubnormal
    ((pCore_isPGroup (p := 2) (G := H)).map H.subtype)

private theorem mem_LSet_of_pSet_of_core_ne
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (M P : Subgroup G)
    (hP : P ∈ SectionThree.PSet M (S : Subgroup G))
    (hcoreM : twoCoreAmbient M ≠ ⊥) :
    M ∈ SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ P :=
    sylow_le_of_isSylowSubgroupIn hP.1.2.1
  have hSM : (S : Subgroup G) ≤ M := hSP.trans hP.1.1
  have hSylowM : IsSylowSubgroupIn (S : Subgroup G) M :=
    isSylowSubgroupIn_of_global_sylow_le S M hSM
  refine ⟨le_top, hSylowM, hcoreM, ?_⟩
  intro hScoreM
  apply hP.1.2.2.2
  apply le_antisymm
  · have hcoreMP : twoCoreAmbient M ≤ P := by
      rw [← hScoreM]
      exact hSP
    rw [hScoreM]
    exact twoCoreAmbient_le_twoCoreAmbient_of_intermediate hP.1.1 hcoreMP
  · exact twoCoreAmbient_le_sylowImage hP.1.2.1

private theorem pSet_mem_of_le
    {G : Type u} [Group G]
    {S U P : Subgroup G}
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hPU : P ≤ U) : P ∈ SectionThree.PSet U S := by
  rcases hP with ⟨⟨_, hSyl, hcore, hproper⟩, hmax⟩
  exact ⟨⟨hPU, hSyl, hcore, hproper⟩, hmax⟩

private theorem pSet_top_of_pSet
    {G : Type u} [Group G]
    {S U P : Subgroup G} (hP : P ∈ SectionThree.PSet U S) :
    P ∈ SectionThree.PSet (⊤ : Subgroup G) S :=
  ⟨⟨le_top, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩

private theorem pstar_residual_subnormal_in_L
    {G : Type u} [Group G] [Finite G]
    {S L P : Subgroup G}
    (hL : L ∈ SectionThree.LSet (⊤ : Subgroup G) S)
    (hP : P ∈ SectionThree.PStarSet L S) :
    IsSubnormalIn (twoResidualAmbient P) L := by
  rcases hP.2 with ⟨M, hM, hsub⟩
  have hLlocal : L ∈ SectionThree.LSet L S :=
    ⟨le_rfl, hL.2.1, hL.2.2.1, hL.2.2.2⟩
  have hLM : L = M := hM.2 L hLlocal hM.1.1
  rwa [hLM]

private theorem solvable_of_mem_LSet
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (L : Subgroup G)
    (hL : SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) L) :
    Group.IsSolvable L := by
  let Q : Subgroup G := twoCoreAmbient L
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hQL : Q ≤ L := Subgroup.map_subtype_le (pCore 2 L)
  have hQnormalL : (Q.subgroupOf L).Normal := by
    unfold Q twoCoreAmbient
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hLN : L ≤ N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mp hQnormalL
  have hSL : (S : Subgroup G) ≤ L :=
    sylow_le_of_isSylowSubgroupIn hL.2.1
  have hSN : (S : Subgroup G) ≤ N := hSL.trans hLN
  have hNtwo : IsTwoLocal N :=
    ⟨Q, hL.2.2.1,
      (pCore_isPGroup (G := L) (p := 2)).map L.subtype, rfl⟩
  have hNsolv : Group.IsSolvable N :=
    (h.local_solvable_characteristicTwo N hNtwo hSN).1
  let _ : Group.IsSolvable N := hNsolv
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hLN)

private theorem three_three_part_a_of_pSet
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : SectionThree.Hypotheses G S)
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsPGroup p
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))) := by
  rcases hP.2 with ⟨B, hBmax, hSB, hBuniq⟩
  have hSP : S ≤ P :=
    sylow_le_of_isSylowSubgroupIn hP.1.2.1
  have hSsubB : S.subgroupOf P ≤ B := by
    intro s hs
    have hsS : (s : G) ∈ S := hs
    obtain ⟨b, hb, hbs⟩ := hSB hsS
    have hbeq : b = s := P.subtype_injective hbs
    simpa [← hbeq] using hb
  let P₀ : Subgroup P := B.normalCore
  have hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact (@Subgroup.normal_le_normalCore P _ B N hN).2 hNB
  have hc := SectionThree.lemma_three_three S h P hP B P₀
    ⟨hBmax, hSsubB, by
      intro B' hB'max hSB'
      apply hBuniq B' hB'max
      intro s hs
      exact Subgroup.mem_map.mpr
        ⟨⟨s, hSP hs⟩, hSB' (show (⟨s, hSP hs⟩ : P) ∈
          S.subgroupOf P from hs), rfl⟩⟩ hP₀ hsolv
  exact hc.part_a

private theorem normal_subgroupOf_subgroupOf
    {G : Type u} [Group G] {H K L : Subgroup G}
    (hHK : H ≤ K) (_hKL : K ≤ L)
    (hN : (H.subgroupOf K).Normal) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono L hHK)]
  intro h k hh hk
  exact (Subgroup.normal_subgroupOf_iff hHK).mp hN
    (h : G) (k : G) hh hk

private theorem twoResidualSubgroup_normal
    {G : Type u} [Group G] (P : Subgroup G) :
    (twoResidualSubgroup P).Normal := by
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N ↦
    Subgroup.normal_iInf_normal (fun hN ↦ hN.1))

/-- **Stellmacher (4.5).**  A member of the global family outside the
`M`-family has a critical partner starred over `M`; under the stated family
containment, `O₂(M) ≤ O₂(C)` and `O₂(C)` is Sylow in the indicated
residual product. -/
public theorem lemma_four_five
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (mSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (cSubgroup S) (S : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hPnot : P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ∃ Pstar : Subgroup G,
      Pstar ∈ SectionThree.PStarSet (mSubgroup S) (S : Subgroup G) ∧
      (P, Pstar) ∈ Lambda S ∧
      ((SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
          SectionThree.PSet (mSubgroup S) (S : Subgroup G)) →
        twoCoreAmbient (mSubgroup S) ≤ twoCoreAmbient (cSubgroup S) ∧
        ∃ E : Subgroup G,
          (E : Set G) =
            (twoResidualAmbient Pstar : Set G) *
              (twoCoreAmbient (cSubgroup S) : Set G) ∧
          IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) := by
  classical
  let Sint : Subgroup G := (S : Subgroup G)
  let M : Subgroup G := mSubgroup S
  let C : Subgroup G := cSubgroup S
  have hPC : P ∈ SectionThree.PSet C Sint := by
    have hPMorC : P ∈ SectionThree.PSet M Sint ∪
        SectionThree.PSet C Sint := by
      rw [← hcover]
      exact hP
    exact hPMorC.resolve_left hPnot
  obtain ⟨Pstar, hPstarAt, hLambda⟩ :=
    lemma_four_four S h P hP hPnot 1 (Or.inr rfl)
  have hPstarOne : Pstar ∈ pOne S := by
    simpa [pAt] using hPstarAt
  have hPstarM : Pstar ∈ SectionThree.PStarSet M Sint := by
    rcases hPstarOne with hPstarM | hPstarOutside
    · exact hPstarM
    · exfalso
      have hPstarC : Pstar ∈ SectionThree.PSet C Sint := by
        have hPstarMorC : Pstar ∈ SectionThree.PSet M Sint ∪
            SectionThree.PSet C Sint := by
          rw [← hcover]
          exact hPstarOutside.1.1
        exact hPstarMorC.resolve_left hPstarOutside.2
      have hSC : Sint ≤ C :=
        (sylow_le_of_isSylowSubgroupIn hPC.1.2.1).trans hPC.1.1
      have hcoreCS : twoCoreAmbient C ≤ Sint :=
        twoCoreAmbient_le_sylowImage
          (isSylowSubgroupIn_of_global_sylow_le S C hSC)
      have hcoreCjoin : twoCoreAmbient C ≤ P ⊔ Pstar :=
        hcoreCS.trans
          ((sylow_le_of_isSylowSubgroupIn hPC.1.2.1).trans le_sup_left)
      have hjoinC : P ⊔ Pstar ≤ C :=
        sup_le hPC.1.1 hPstarC.1.1
      have hcoreCcoreJoin :
          twoCoreAmbient C ≤ twoCoreAmbient (P ⊔ Pstar) :=
        twoCoreAmbient_le_twoCoreAmbient_of_intermediate hjoinC hcoreCjoin
      apply twoCore_cSubgroup_ne_bot S h.even_order
      have hcoreCbot : twoCoreAmbient C = ⊥ := by
        apply le_antisymm
        · exact hcoreCcoreJoin.trans_eq hLambda.2.2
        · exact bot_le
      simpa [C] using hcoreCbot
  refine ⟨Pstar, hPstarM, hLambda, ?_⟩
  intro hstarCM
  have hcoreMne : twoCoreAmbient M ≠ ⊥ := by
    simpa [M] using (lemma_four_one S h).part_b
  have hcoreCne : twoCoreAmbient C ≠ ⊥ := by
    simpa [C] using twoCore_cSubgroup_ne_bot S h.even_order
  have hML : M ∈ SectionThree.LSet (⊤ : Subgroup G) Sint :=
    mem_LSet_of_pSet_of_core_ne S M Pstar hPstarM.1 hcoreMne
  have hCL : C ∈ SectionThree.LSet (⊤ : Subgroup G) Sint :=
    mem_LSet_of_pSet_of_core_ne S C P hPC hcoreCne
  have h42M := lemma_four_two S h M hML
  have h42C := lemma_four_two S h C hCL
  have hcoreMC : twoCoreAmbient M ≤ twoCoreAmbient C := by
    calc
      twoCoreAmbient M = localD M Sint := h42M.2.1.symm
      _ ≤ localDStar C Sint := by
        rw [localD, localDStar]
        apply le_sInf
        intro D hD
        rcases hD with ⟨Q, hQ, rfl⟩
        apply sInf_le
        exact ⟨Q, hstarCM hQ, rfl⟩
      _ = localD C Sint := h42C.1.symm
      _ = twoCoreAmbient C := h42C.2.1
  refine ⟨hcoreMC, ?_⟩
  let A : Subgroup G := twoResidualAmbient Pstar
  let Q : Subgroup G := twoCoreAmbient C
  let E : Subgroup G := A ⊔ Q
  have hPstarMle : Pstar ≤ M := hPstarM.1.1.1
  have hAMsub : IsSubnormalIn A M := by
    simpa [A] using pstar_residual_subnormal_in_L hML hPstarM
  have hcoreAA : twoCoreAmbient A ≤ A :=
    Subgroup.map_subtype_le (pCore 2 A)
  have hcoreAnormalA : ((twoCoreAmbient A).subgroupOf A).Normal :=
    twoCoreAmbient_normal_subgroupOf A
  have hcoreAsubM : ((twoCoreAmbient A).subgroupOf M).IsSubnormal := by
    apply Subgroup.IsSubnormal.step _ (A.subgroupOf M)
      (Subgroup.subgroupOf_mono M hcoreAA) hAMsub.2
    exact normal_subgroupOf_subgroupOf hcoreAA hAMsub.1 hcoreAnormalA
  have hcoreAM : twoCoreAmbient A ≤ twoCoreAmbient M :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn M (twoCoreAmbient A) 2
      (hcoreAA.trans hAMsub.1) hcoreAsubM
      ((pCore_isPGroup (p := 2) (G := A)).map A.subtype)
  have hcoreAQ : twoCoreAmbient A ≤ Q := hcoreAM.trans hcoreMC
  have hSPstar : Sint ≤ Pstar :=
    sylow_le_of_isSylowSubgroupIn hPstarM.1.1.2.1
  have hSC : Sint ≤ C :=
    (sylow_le_of_isSylowSubgroupIn hPC.1.2.1).trans hPC.1.1
  have hQS : Q ≤ Sint := by
    exact twoCoreAmbient_le_sylowImage
      (isSylowSubgroupIn_of_global_sylow_le S C hSC)
  have hQPstar : Q ≤ Pstar := hQS.trans hSPstar
  have hAPstar : A ≤ Pstar :=
    Subgroup.map_subtype_le (twoResidualSubgroup Pstar)
  have hAnormalPstar : (A.subgroupOf Pstar).Normal := by
    unfold A twoResidualAmbient
    rw [subgroupOf_map_subtype_eq]
    exact twoResidualSubgroup_normal Pstar
  have hPstarSolv : Group.IsSolvable Pstar := by
    let _ : Group.IsSolvable M := solvable_of_mem_LSet S h M hML
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hPstarMle)
  have hThree : SectionThree.Hypotheses G Sint :=
    ⟨h.even_order, S.ne_bot_of_dvd_card h.even_order.two_dvd,
      S.isPGroup'⟩
  have hpquot := three_three_part_a_of_pSet Sint hThree Pstar
    (pSet_top_of_pSet hPstarM.1) hPstarSolv
  have hASylow : IsSylowSubgroupIn (twoCoreAmbient A) A := by
    simpa [A] using
      twoCoreAmbient_isSylow_twoResidualAmbient Pstar hpquot
  have hQ2 : IsPGroup 2 Q := by
    change IsPGroup 2 (twoCoreAmbient C)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hQSylow : IsSylowSubgroupIn Q E := by
    simpa [E] using isSylow_two_of_normal_product Pstar A Q
      hAPstar hQPstar hAnormalPstar hASylow hcoreAQ hQ2
  have hPstarNormalizer : Pstar ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAPstar).mp hAnormalPstar
  refine ⟨E, ?_, hQSylow⟩
  exact Subgroup.coe_mul_of_right_le_normalizer_left A Q
    (hQPstar.trans hPstarNormalizer)

end Stellmacher.SectionFour
