module

public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# Stellmacher's Lemma 4.2

For `L ∈ LSet ⊤ S`, the intersections of the 2-cores over `PSet L S`
and over its starred subfamily both equal `O₂(L)`. Consequently the global
intersection over `PSet ⊤ S` can be taken over the 2-cores of the maximal
members of `LSet ⊤ S`.

The proof follows Stellmacher's Fitting argument. Result (3.7) expresses
`[F(L/O₂(L)), S̄]` as the join of the starred residual images. Solvability
first shows this commutator is nontrivial, so the starred family is nonempty
and its core intersection lies in `S`. For every starred `P`, the commutator
of `O²(P)` with that intersection lies in `O₂(P)`; its quotient image is
simultaneously a 2-group and contained in the odd-order Fitting subgroup, so
it already lies in `O₂(L)`. Coprime action and self-centralization of the
Fitting subgroup then force the entire starred intersection into `O₂(L)`.
The reverse inclusions are the standard monotonicity of 2-cores sharing the
same Sylow subgroup. The final equality uses maximal elements of the finite
subgroup lattice.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (4.2),
journal page 25.
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionFour

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem localD_le_localDStar (L S : Subgroup G) :
    localD L S ≤ localDStar L S := by
  rw [localD, localDStar]
  apply le_sInf
  intro D hD
  obtain ⟨P, hP, rfl⟩ := hD
  apply sInf_le
  exact ⟨P, hP.1, rfl⟩

omit [Finite G] in
private theorem twoCoreAmbient_le_of_le_of_common_sylow
    (L P S : Subgroup G) (hPL : P ≤ L)
    (hSylL : IsSylowSubgroupIn S L)
    (hSylP : IsSylowSubgroupIn S P) :
    twoCoreAmbient L ≤ twoCoreAmbient P := by
  obtain ⟨TL, hTL⟩ := hSylL
  obtain ⟨TP, hTP⟩ := hSylP
  have hCoreLS : twoCoreAmbient L ≤ S := by
    rw [← hTL]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal TL)
  have hSP : S ≤ P := by
    rw [← hTP]
    exact Subgroup.map_subtype_le (TP : Subgroup P)
  have hCoreLP : twoCoreAmbient L ≤ P := hCoreLS.trans hSP
  have hCoreLL : twoCoreAmbient L ≤ L :=
    Subgroup.map_subtype_le (pCore 2 L)
  have hnormalL : ((twoCoreAmbient L).subgroupOf L).Normal := by
    rw [← Subgroup.comap_subtype, twoCoreAmbient,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    exact (inferInstance : (pCore 2 L).Normal)
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
private theorem twoCoreAmbient_le_localD
    (L S : Subgroup G) (hSylL : IsSylowSubgroupIn S L) :
    twoCoreAmbient L ≤ localD L S := by
  rw [localD]
  apply le_sInf
  intro D hD
  obtain ⟨P, hP, rfl⟩ := hD
  exact twoCoreAmbient_le_of_le_of_common_sylow L P S
    hP.1.1 hSylL hP.1.2.1

omit [Finite G] in
private theorem twoCoreAmbient_le_sylowImage
    {S P : Subgroup G} (hSylow : IsSylowSubgroupIn S P) :
    twoCoreAmbient P ≤ S := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)

private theorem pCore_quotient_pCore_eq_bot
    (Q : Type u) [Group Q] [Finite Q] :
    pCore 2 (Q ⧸ pCore 2 Q) = ⊥ := by
  let O : Subgroup Q := pCore 2 Q
  let q : Q →* Q ⧸ O := QuotientGroup.mk' O
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := Q) (p := 2) O (pCore_isPGroup (G := Q) (p := 2))
  have hmapbot : (pCore 2 Q).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore 2 Q)).2
    simp [q, O, QuotientGroup.ker_mk']
  dsimp [q, O] at hmapbot
  exact hmap.symm.trans hmapbot

private theorem fitting_odd_of_pCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q]
    (hO : pCore 2 Q = ⊥) : Odd (Nat.card (fittingSubgroup Q)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup Q := fittingSubgroup Q
  have hFnorm : F.Normal := inferInstance
  let OF : Subgroup F := pCore 2 F
  have hOFmapNormal : (OF.map F.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hOFmapP : IsPGroup 2 (OF.map F.subtype) :=
    (pCore_isPGroup (G := F) (p := 2)).map F.subtype
  have hOFmapLe : OF.map F.subtype ≤ pCore 2 Q :=
    le_sSup ⟨hOFmapNormal, hOFmapP⟩
  have hOFbot : OF = ⊥ := by
    apply (Subgroup.map_injective F.subtype_injective)
    rw [Subgroup.map_bot]
    rw [hO] at hOFmapLe
    exact le_antisymm hOFmapLe bot_le
  apply Nat.not_even_iff_odd.mp
  intro heven
  let SF : Sylow 2 F := Classical.choice (Sylow.nonempty (p := 2) (G := F))
  have hSFne : (SF : Subgroup F) ≠ ⊥ :=
    SF.ne_bot_of_dvd_card heven.two_dvd
  have hSFnorm : (SF : Subgroup F).Normal :=
    Group.IsNilpotent.sylow_normal (by infer_instance) 2 SF
  have hSFle : (SF : Subgroup F) ≤ OF :=
    le_sSup ⟨hSFnorm, SF.isPGroup'⟩
  rw [hOFbot] at hSFle
  exact hSFne (le_antisymm hSFle bot_le)

private theorem eq_bot_of_le_of_isPGroup_two_of_odd_card
    (P K : Subgroup G) (hPK : P ≤ K)
    (hP2 : IsPGroup 2 P) (hKodd : Odd (Nat.card K)) :
    P = ⊥ := by
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (Nat.card K) := by
    rw [hn]
    exact hKodd.coprime_two_left.pow_left n
  have hinf : P ⊓ K = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rwa [inf_eq_left.mpr hPK] at hinf

private theorem commutator_double_eq_self_of_coprime_solvable
    (P K : Subgroup G) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let _ : Subgroup.Normalizes P K := ⟨hPK⟩
  let _ : MulDistribMulAction P K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup K := commutatorAction (A := P) (G := K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := P) (G := K) = C :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := K) (A := P) hsolv hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := P) (G := K)).map K.subtype ≤
        ⁅⁅K, P⁆, P⁆ := by
    let X : Set K := {x : K | ∃ a : P, ∃ k : K,
      k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (commutatorAction₂ (A := P) (G := K)).map K.subtype =
          (Subgroup.closure X).map K.subtype := by rfl
      _ = Subgroup.closure (K.subtype '' X) := by
        simpa using (MonoidHom.map_closure (f := K.subtype) X)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, k, hkC, rfl⟩
        have hkX : (k : G) ∈ ⁅K, P⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
        have hgen : ⁅((k : K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator
            (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          mul_assoc] using hgen
  have hreverse : ⁅K, P⁆ ≤ ⁅⁅K, P⁆, P⁆ := by
    calc
      ⁅K, P⁆ = C.map K.subtype := hCmap.symm
      _ = (commutatorAction₂ (A := P) (G := K)).map K.subtype := by
        rw [hC2eq]
      _ ≤ ⁅⁅K, P⁆, P⁆ := hcomm₂_le
  exact le_antisymm hXle hreverse

private theorem solvable_of_mem_LSet
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
  have hSL : (S : Subgroup G) ≤ L := by
    obtain ⟨T, hT⟩ := hL.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le (T : Subgroup L)
  have hSN : (S : Subgroup G) ≤ N := hSL.trans hLN
  have hNtwo : IsTwoLocal N :=
    ⟨Q, hL.2.2.1,
      (pCore_isPGroup (G := L) (p := 2)).map L.subtype, rfl⟩
  have hNsolv : Group.IsSolvable N :=
    (h.local_solvable_characteristicTwo N hNtwo hSN).1
  let _ : Group.IsSolvable N := hNsolv
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hLN)

private theorem localDStar_le_twoCoreAmbient
    (S : Sylow 2 G) (h : Hypotheses G S)
    (L : Subgroup G)
    (hL : SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) L) :
    localDStar L (S : Subgroup G) ≤ twoCoreAmbient L := by
  classical
  let Sint : Subgroup G := (S : Subgroup G)
  let q : L →* L ⧸ pCore 2 L := QuotientGroup.mk' (pCore 2 L)
  let Sbar : Subgroup (L ⧸ pCore 2 L) := (Sint.subgroupOf L).map q
  let F : Subgroup (L ⧸ pCore 2 L) := fittingSubgroup (L ⧸ pCore 2 L)
  let C : Subgroup (L ⧸ pCore 2 L) := ⁅F, Sbar⁆
  let D : Subgroup G := localDStar L Sint
  have hSL : Sint ≤ L := by
    change (S : Subgroup G) ≤ L
    obtain ⟨T, hT⟩ := hL.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le (T : Subgroup L)
  have hThreeHyp : SectionThree.Hypotheses G Sint :=
    ⟨h.even_order,
      S.ne_bot_of_dvd_card h.even_order.two_dvd,
      S.isPGroup'⟩
  have hLsolv : Group.IsSolvable L := solvable_of_mem_LSet S h L hL
  have hthree := SectionThree.lemma_three_seven Sint hThreeHyp L hL hLsolv
  change C = ⨆ P : {P : Subgroup G //
      P ∈ SectionThree.PStarSet L Sint},
        SectionThree.twoResidualImageInQuotient L P at hthree
  have hSbar2 : IsPGroup 2 Sbar := by
    have hSint2 : IsPGroup 2 (Sint.subgroupOf L) :=
      S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
    exact hSint2.map q
  have hOquot : pCore 2 (L ⧸ pCore 2 L) = ⊥ :=
    pCore_quotient_pCore_eq_bot L
  have hFodd : Odd (Nat.card F) := by
    simpa [F] using fitting_odd_of_pCore_eq_bot hOquot
  have hC_le_F : C ≤ F :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.le_normalizer_of_normal :
        Sbar ≤ Subgroup.normalizer (F : Set _))
  have hquotSolv : Group.IsSolvable (L ⧸ pCore 2 L) :=
    Group.isSolvable_of_surjective
      (f := q) (QuotientGroup.mk'_surjective (pCore 2 L))
  have hCne : C ≠ ⊥ := by
    intro hCbot
    have hFSbot : ⁅F, Sbar⁆ = ⊥ := by simpa [C] using hCbot
    have hFcentS : F ≤ Subgroup.centralizer (Sbar : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFSbot
    have hScentF : Sbar ≤ Subgroup.centralizer (F : Set _) :=
      Subgroup.le_centralizer_iff.mp hFcentS
    have hSbarF : Sbar ≤ F := hScentF.trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hquotSolv)
    have hSbarBot : Sbar = ⊥ :=
      eq_bot_of_le_of_isPGroup_two_of_odd_card Sbar F hSbarF hSbar2 hFodd
    have hSintKer : Sint.subgroupOf L ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (f := q) (H := Sint.subgroupOf L)).mp
        hSbarBot
    have hSintCore : Sint.subgroupOf L ≤ pCore 2 L := by
      simpa [q, QuotientGroup.ker_mk'] using hSintKer
    have hSCore : Sint ≤ twoCoreAmbient L := by
      calc
        Sint = (Sint.subgroupOf L).map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hSL).symm
        _ ≤ (pCore 2 L).map L.subtype := Subgroup.map_mono hSintCore
        _ = twoCoreAmbient L := rfl
    exact hL.2.2.2 (le_antisymm hSCore
      (twoCoreAmbient_le_sylowImage hL.2.1))
  let Idx := {P : Subgroup G // P ∈ SectionThree.PStarSet L Sint}
  have hIdx : Nonempty Idx := by
    by_contra hn
    let _ : IsEmpty Idx := ⟨fun x ↦ hn ⟨x⟩⟩
    have hjoinBot :
        (⨆ P : Idx, SectionThree.twoResidualImageInQuotient L P) = ⊥ := by
      simp [iSup_of_empty]
    apply hCne
    exact hthree.trans hjoinBot
  let _ : Nonempty Idx := hIdx
  let P₀ : Idx := Classical.choice hIdx
  have hDCoreP₀ : D ≤ twoCoreAmbient (P₀ : Subgroup G) := by
    apply sInf_le
    exact ⟨(P₀ : Subgroup G), P₀.property, rfl⟩
  have hDS : D ≤ Sint :=
    hDCoreP₀.trans (twoCoreAmbient_le_sylowImage P₀.property.1.1.2.1)
  have hDL : D ≤ L := hDS.trans hSL
  let Dbar : Subgroup (L ⧸ pCore 2 L) := (D.subgroupOf L).map q
  have hDbarSbar : Dbar ≤ Sbar := by
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hDS)
  have hDbar2 : IsPGroup 2 Dbar :=
    (hSbar2.to_subgroup (Dbar.subgroupOf Sbar)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hDbarSbar)
  have hCDbar : ⁅C, Dbar⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [hthree]
    refine iSup_le fun P ↦ ?_
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    let A : Subgroup G := twoResidualAmbient (P : Subgroup G)
    let OP : Subgroup G := twoCoreAmbient (P : Subgroup G)
    let K : Subgroup G := A ⊓ OP
    have hPL : (P : Subgroup G) ≤ L := P.property.1.1.1
    have hSP : Sint ≤ (P : Subgroup G) := by
      change (S : Subgroup G) ≤ (P : Subgroup G)
      obtain ⟨T, hT⟩ := P.property.1.1.2.1
      intro x hx
      have hxmap : x ∈ (T : Subgroup (P : Subgroup G)).map
          (P : Subgroup G).subtype := by
        rw [hT]
        exact hx
      exact (Subgroup.map_subtype_le (T : Subgroup (P : Subgroup G))) hxmap
    have hAP : A ≤ (P : Subgroup G) :=
      Subgroup.map_subtype_le (twoResidualSubgroup (P : Subgroup G))
    have hAL : A ≤ L := hAP.trans hPL
    have hDP : D ≤ (P : Subgroup G) := hDS.trans hSP
    have hDOP : D ≤ OP := by
      change localDStar L Sint ≤ OP
      apply sInf_le
      exact ⟨(P : Subgroup G), P.property, rfl⟩
    have hAnormalP : (A.subgroupOf (P : Subgroup G)).Normal := by
      unfold A twoResidualAmbient
      rw [subgroupOf_map_subtype_eq]
      unfold twoResidualSubgroup
      rw [sInf_eq_iInf]
      exact Subgroup.normal_iInf_normal (fun N ↦
        Subgroup.normal_iInf_normal (fun hN ↦ hN.1))
    have hOPnormalP : (OP.subgroupOf (P : Subgroup G)).Normal := by
      unfold OP twoCoreAmbient
      rw [subgroupOf_map_subtype_eq]
      infer_instance
    have hPnormA : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le
          (twoResidualSubgroup (P : Subgroup G)))).mp
          hAnormalP
    have hPnormOP : (P : Subgroup G) ≤ Subgroup.normalizer (OP : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le (pCore 2 (P : Subgroup G)))).mp
          hOPnormalP
    have hcommA : ⁅A, D⁆ ≤ A :=
      (Subgroup.le_normalizer_iff_commutator_le_left).mp
        (hDP.trans hPnormA)
    have hcommOP : ⁅A, D⁆ ≤ OP := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hDOP le_rfl).trans
        ((Subgroup.le_normalizer_iff_commutator_le_left).mp
          (hAP.trans hPnormOP))
    have hcommK : ⁅A, D⁆ ≤ K := le_inf hcommA hcommOP
    have hKL : K ≤ L := inf_le_left.trans hAL
    have hOP2 : IsPGroup 2 OP :=
      (pCore_isPGroup (G := (P : Subgroup G)) (p := 2)).map
        (P : Subgroup G).subtype
    have hK2int : IsPGroup 2 (K.subgroupOf OP) :=
      hOP2.to_subgroup (K.subgroupOf OP)
    have hK2 : IsPGroup 2 K :=
      hK2int.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right)
    let Kbar : Subgroup (L ⧸ pCore 2 L) := (K.subgroupOf L).map q
    have hKbar2 : IsPGroup 2 Kbar := by
      exact (hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm).map q
    have hKbarAbar : Kbar ≤
        SectionThree.twoResidualImageInQuotient L (P : Subgroup G) := by
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono L inf_le_left)
    have hAbarC :
        SectionThree.twoResidualImageInQuotient L (P : Subgroup G) ≤ C := by
      rw [hthree]
      exact le_iSup
        (fun Q : {Q : Subgroup G // Q ∈ SectionThree.PStarSet L Sint} ↦
          SectionThree.twoResidualImageInQuotient L Q) P
    have hKbarF : Kbar ≤ F := hKbarAbar.trans (hAbarC.trans hC_le_F)
    have hKbarBot : Kbar = ⊥ :=
      eq_bot_of_le_of_isPGroup_two_of_odd_card Kbar F
        hKbarF hKbar2 hFodd
    have hKintCore : K.subgroupOf L ≤ pCore 2 L := by
      have hker := (Subgroup.map_eq_bot_iff
        (f := q) (H := K.subgroupOf L)).mp hKbarBot
      simpa [q, QuotientGroup.ker_mk'] using hker
    have hKCore : K ≤ twoCoreAmbient L := by
      calc
        K = (K.subgroupOf L).map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hKL).symm
        _ ≤ (pCore 2 L).map L.subtype := Subgroup.map_mono hKintCore
        _ = twoCoreAmbient L := rfl
    have hcommCore : ⁅A, D⁆ ≤ twoCoreAmbient L := hcommK.trans hKCore
    have hcommInt :
        ⁅A.subgroupOf L, D.subgroupOf L⁆ ≤ pCore 2 L := by
      apply Subgroup.map_subtype_le_map_subtype.mp
      rw [commutator_subgroupOf_map_eq L D A hDL hAL]
      exact hcommCore
    have hmapped := Subgroup.map_mono (f := q) hcommInt
    rw [Subgroup.map_commutator] at hmapped
    change ⁅SectionThree.twoResidualImageInQuotient L (P : Subgroup G),
      Dbar⁆ ≤ (pCore 2 L).map q at hmapped
    have hcoreMapBot : (pCore 2 L).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore 2 L)).2
      simp [q, QuotientGroup.ker_mk']
    rw [hcoreMapBot] at hmapped
    exact le_antisymm hmapped bot_le
  have hFDbar_le_C : ⁅F, Dbar⁆ ≤ C :=
    Subgroup.commutator_mono le_rfl hDbarSbar
  have hdoubleBot : ⁅⁅F, Dbar⁆, Dbar⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono hFDbar_le_C le_rfl).trans
        (le_of_eq hCDbar)
    · exact bot_le
  have hDbarNormF : Dbar ≤ Subgroup.normalizer (F : Set _) :=
    hDbarSbar.trans Subgroup.le_normalizer_of_normal
  have hDbarFcop : Nat.Coprime (Nat.card Dbar) (Nat.card F) := by
    obtain ⟨n, hn⟩ := hDbar2.exists_card_eq
    rw [hn]
    exact hFodd.coprime_two_left.pow_left n
  have hdoubleEq : ⁅⁅F, Dbar⁆, Dbar⁆ = ⁅F, Dbar⁆ :=
    commutator_double_eq_self_of_coprime_solvable Dbar F
      hDbarNormF hDbarFcop IsNilpotent.to_isSolvable
  have hFDbarBot : ⁅F, Dbar⁆ = ⊥ := hdoubleEq.symm.trans hdoubleBot
  have hFcentD : F ≤ Subgroup.centralizer (Dbar : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hFDbarBot
  have hDcentF : Dbar ≤ Subgroup.centralizer (F : Set _) :=
    Subgroup.le_centralizer_iff.mp hFcentD
  have hDbarF : Dbar ≤ F := hDcentF.trans
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hquotSolv)
  have hDbarBot : Dbar = ⊥ :=
    eq_bot_of_le_of_isPGroup_two_of_odd_card Dbar F
      hDbarF hDbar2 hFodd
  have hDintCore : D.subgroupOf L ≤ pCore 2 L := by
    have hker := (Subgroup.map_eq_bot_iff
      (f := q) (H := D.subgroupOf L)).mp hDbarBot
    simpa [q, QuotientGroup.ker_mk'] using hker
  calc
    D = (D.subgroupOf L).map L.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hDL).symm
    _ ≤ (pCore 2 L).map L.subtype := Subgroup.map_mono hDintCore
    _ = twoCoreAmbient L := rfl

public theorem lemma_four_two
    (S : Sylow 2 G) (h : Hypotheses G S)
    (L : Subgroup G)
    (hL : SectionThree.LSet (⊤ : Subgroup G) (S : Subgroup G) L) :
    localD L (S : Subgroup G) = localDStar L (S : Subgroup G) ∧
      localD L (S : Subgroup G) = twoCoreAmbient L ∧
      dSubgroup S =
        sInf {D : Subgroup G |
          ∃ L' : Subgroup G,
            L' ∈ SectionThree.maxLSet (⊤ : Subgroup G) (S : Subgroup G) ∧
              D = twoCoreAmbient L'} := by
  let Sint : Subgroup G := (S : Subgroup G)
  have hcoreD : twoCoreAmbient L ≤ localD L Sint :=
    twoCoreAmbient_le_localD L Sint hL.2.1
  have hDstar : localDStar L Sint ≤ twoCoreAmbient L :=
    localDStar_le_twoCoreAmbient S h L hL
  have hDstarFamily : localD L Sint ≤ localDStar L Sint :=
    localD_le_localDStar L Sint
  have hlocalD : localD L Sint = twoCoreAmbient L :=
    le_antisymm (hDstarFamily.trans hDstar) hcoreD
  have hlocalStar : localD L Sint = localDStar L Sint :=
    le_antisymm hDstarFamily (hDstar.trans hcoreD)
  refine ⟨hlocalStar, hlocalD, ?_⟩
  let MInf : Subgroup G :=
    sInf {D : Subgroup G |
      ∃ L' : Subgroup G,
        L' ∈ SectionThree.maxLSet (⊤ : Subgroup G) Sint ∧
          D = twoCoreAmbient L'}
  change dSubgroup S = MInf
  apply le_antisymm
  · rw [dSubgroup]
    apply le_sInf
    intro D₀ hD₀
    obtain ⟨L', hL'max, rfl⟩ := hD₀
    have hlocalL' : localD L' Sint = twoCoreAmbient L' := by
      apply le_antisymm
      · exact (localD_le_localDStar L' Sint).trans
          (localDStar_le_twoCoreAmbient S h L' hL'max.1)
      · exact twoCoreAmbient_le_localD L' Sint hL'max.1.2.1
    rw [← hlocalL', localD]
    apply le_sInf
    intro D₁ hD₁
    obtain ⟨P, hP, rfl⟩ := hD₁
    apply sInf_le
    exact ⟨P,
      ⟨⟨le_top, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩,
      rfl⟩
  · rw [dSubgroup]
    apply le_sInf
    intro D₀ hD₀
    obtain ⟨P, hP, rfl⟩ := hD₀
    obtain ⟨M, hPM, hMmax⟩ := Finite.exists_le_maximal hP.1
    have hMmaxSet :
        M ∈ SectionThree.maxLSet (⊤ : Subgroup G) Sint := by
      refine ⟨hMmax.prop, ?_⟩
      intro M' hM' hMM'
      exact (hMmax.eq_of_le hM' hMM').symm
    have hMInfCore : MInf ≤ twoCoreAmbient M := by
      apply sInf_le
      exact ⟨M, hMmaxSet, rfl⟩
    exact hMInfCore.trans
      (twoCoreAmbient_le_of_le_of_common_sylow M P Sint hPM
        hMmax.prop.2.1 hP.1.2.1)

end Stellmacher.SectionFour
