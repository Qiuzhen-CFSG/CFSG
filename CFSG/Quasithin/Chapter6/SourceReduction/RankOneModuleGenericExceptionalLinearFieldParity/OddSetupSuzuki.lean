module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import Theory.GroupTheory.CComponent.OddRankIsolation
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups
public import Theory.SpecificGroups.Suzuki.BinaryLinearActions
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient

/-!
# The nonsolvable quotient-centralizer in source 5.1.16(2)

The literal kernel C of the action of N_G(K) on K/O₂(K) has order prime
to three. The PSL₃(4) factor also leaves at most one unit of five-rank
in C. The complete A.3.6 catalogue makes every C-component Suzuki;
rank addition gives uniqueness, and A.3.9 identifies it with C^∞.
The resulting isomorphism is on the actual quotient of its image in G.

Characteristic-two uniqueness gives N_G(C^∞)=N_G(K). If C^∞ lay in
N_G(L), its perfect Suzuki-cover action on L/O₂(L) would be trivial.
The normal two-core O₂(L) lies in T and normalizes C^∞. Perfect
normalizer lifting would then put L in N_G(C^∞), contradicting the
distinct uniqueness normalizers of L and K.

Thus this module proves the first two assertions of 5.1.16(2). The final
Cartan exclusion via the genuine F.1.1/F.1.12 argument, and its use to
prove solvability, remain with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.16(2), printed pp.639–640,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem suzuki_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2*m+1)) ^ 2 = 4 * 16 ^ m := by
    rw [← pow_mul]
    have he : (2*m+1)*2 = 2+4*m := by omega
    rw [he,pow_add,pow_mul]
    norm_num
  rw [he,Nat.add_mod,Nat.mul_mod]
  have h16 : 16 ^ m % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ m) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  rw [h16]

/-- The PSL₃(4) factor leaves at most one unit of five-rank in its quotient-centralizer. -/
theorem residual_kernel_five_rank_le_one (K : Subgroup G)
    (hN : IsStronglyQuasithin (normalizer (K : Set G)))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    primeRank 5 (normalizerQuotientAction K (pCore 2 K)).ker ≤ 1 := by
  let N := normalizer (K : Set G)
  let a := normalizerQuotientAction K (pCore 2 K)
  let C := a.ker.map N.subtype
  have hCN : C ≤ N := map_subtype_le _
  have hcomm : ⁅C,K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro c hc k hk
    obtain ⟨x,hx,rfl⟩ := hc
    have he : a x = 1 := hx
    have hf := congrArg (fun f : MulAut (K ⧸ pCore 2 K) =>
      f (QuotientGroup.mk' (pCore 2 K) ⟨k,hk⟩)) he
    simp only [a,normalizerQuotientAction,MonoidHom.comp_apply,
      quotientAut_apply_mk,MulAut.one_apply] at hf
    have hh : K.normalizerMonoidHom x ⟨k,hk⟩ / ⟨k,hk⟩ ∈ pCore 2 K :=
      QuotientGroup.eq_iff_div_mem.mp hf
    have hh' := mem_map_of_mem K.subtype hh
    change (((K.normalizerMonoidHom x) ⟨k,hk⟩ : K) : G) / k ∈ K.pCoreIn 2 at hh'
    rw [normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv] at hh'
    exact hh'
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 5) C K hCN
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcomm)
    (by
      obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
      let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
      rw [Nat.card_congr (centerCongr e).toEquiv,
        Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)]
      simp)
  have hupper : primeRank 5 (C ⊔ K : Subgroup G) ≤ 2 :=
    (primeRank_mono 5 (sup_le hCN K.le_normalizer)).trans
      (hN 5 Nat.prime_five (by decide))
  have hd : 5 ∣ Nat.card K := by
    apply dvd_trans _ (pCore 2 K).card_quotient_dvd_card
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
      (by rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
        hF,Matrix.PSL3Four.card_F])
    rw [Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv,
      Matrix.PSL3Four.card_PSL]
    decide
  have hpos : primeRank 5 K ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  have he : primeRank 5 a.ker = primeRank 5 C :=
    primeRank_congr 5 (a.ker.equivMapOfInjective N.subtype N.subtype_injective)
  change primeRank 5 a.ker ≤ 1
  omega

/-- In an SQTK group of order prime to three and five-rank at most one, the nonsolvable
residual is the unique C-component and has its actual Suzuki quotient. -/
private theorem three_prime_rank_one_residual_suzuki
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (h3 : Nat.Coprime 3 (Nat.card G)) (h5 : primeRank 5 G ≤ 1)
    (hns : ¬ Group.IsSolvable G) :
    (solvableResidual G).IsCComponent ∧
      (∀ J : Subgroup G, J.IsCComponent → J = solvableResidual G) ∧
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty
        (((solvableResidual G) ⧸ pCore 2 (solvableResidual G)) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have model (J : Subgroup G) (hJ : J.IsCComponent) :
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((J ⧸ pCore 2 J) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.component_suzuki_quotient
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hQ hJ
      (h3.of_dvd_right J.card_subgroup_dvd_card)
  have hd (J : Subgroup G) (hJ : J.IsCComponent) : 5 ∣ Nat.card (J ⧸ pCore 2 J) := by
    obtain ⟨m,hm,⟨e⟩⟩ := model J hJ
    rw [Nat.card_congr e.toEquiv]
    exact suzuki_five_dvd m (by omega)
  obtain ⟨J,hJ⟩ := exists_isCComponent_of_not_isSolvable hns
  obtain ⟨m,hm,⟨e⟩⟩ := model J hJ
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect (J ⧸ pCore 2 J) := inferInstance
  have hz : center (J ⧸ pCore 2 J) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh))
  let : IsQuasisimple (J ⧸ pCore 2 J) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hr : primeRank 5 G ≤ primeRank 5 (J ⧸ pCore 2 J) := by
    have hne : primeRank 5 (J ⧸ pCore 2 J) ≠ 0 :=
      fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh (hd J hJ)
    omega
  have hu (D : Subgroup G) (hD : D.IsCComponent) : D = J := by
    by_contra hne
    have hc := hJ.other_coprime_of_full_odd_rank (by decide : Odd 5) hz hr hD hne
    exact Nat.prime_five.coprime_iff_not_dvd.mp hc
      ((hd D hD).trans (pCore 2 D).card_quotient_dvd_card)
  have hgen : cComponentLayer G = solvableResidual G :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO) hQ
  have he : solvableResidual G = J := by
    rw [← hgen]
    exact le_antisymm (sSup_le (fun D hD => (hu D hD).le)) (le_cComponentLayer hJ)
  rw [he]
  exact ⟨hJ,hu,m,hm,⟨e⟩⟩


/-- The literal ambient quotient-centralizer C_K. -/
@[expose] def quotientCentralizer (K : Subgroup G) : Subgroup G :=
  (normalizerQuotientAction K (pCore 2 K)).ker.map (normalizer (K : Set G)).subtype

/-- The actual terminal derived subgroup C_K^∞, embedded in G. -/
@[expose] def quotientCentralizerResidual (K : Subgroup G) : Subgroup G :=
  (solvableResidual (quotientCentralizer K)).map (quotientCentralizer K).subtype

omit [Finite G] in
/-- Normality here is relative to N_G(K), rather than to G. -/
theorem normalizer_le_normalizer_quotientCentralizerResidual (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (quotientCentralizerResidual K : Set G) := by
  have hc : normalizer (K : Set G) ≤ normalizer (quotientCentralizer K : Set G) := by
    change normalizer (K : Set G) ≤ normalizer
      ((normalizerQuotientAction K (pCore 2 K)).ker.map (normalizer (K : Set G)).subtype : Set G)
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (normalizerQuotientAction K (pCore 2 K)).ker.le_normalizer_map
        (normalizer (K : Set G)).subtype
  exact hc.trans (normalizer_le_normalizer_characteristic_image
    (quotientCentralizer K) (solvableResidual (quotientCentralizer K)))

/-- The first assertion of 5.1.16(2), with the genuine matrix quotient and
unique component of the literal kernel; the exclusion of this case is separate. -/
theorem nonsolvable_quotientCentralizer_residual_suzuki (K : Subgroup G)
    (hN : IsSQTK KnownSimple.IsKnownSimple (normalizer (K : Set G)))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hns : ¬ Group.IsSolvable (normalizerQuotientAction K (pCore 2 K)).ker) :
    (solvableResidual (quotientCentralizer K)).IsCComponent ∧
      (∀ J : Subgroup (quotientCentralizer K), J.IsCComponent →
        J = solvableResidual (quotientCentralizer K)) ∧
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((quotientCentralizerResidual K ⧸ pCore 2 (quotientCentralizerResidual K)) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let N := normalizer (K : Set G)
  let a := normalizerQuotientAction K (pCore 2 K)
  let C := quotientCentralizer K
  let e : a.ker ≃* C := a.ker.equivMapOfInjective N.subtype N.subtype_injective
  have hs : IsSQTK KnownSimple.IsKnownSimple C := (IsSQTK.equiv e).mp (hN.subgroup a.ker)
  have h3 : Nat.Coprime 3 (Nat.card C) := by
    rw [← Nat.card_congr e.toEquiv]
    exact CubicEscape.quotientAction_kernel_three_prime K hN.stronglyQuasithin hm
  have h5 : primeRank 5 C ≤ 1 := by
    rw [← primeRank_congr 5 e]
    exact residual_kernel_five_rank_le_one K hN.stronglyQuasithin hm
  have hnsC : ¬ Group.IsSolvable C := by
    intro hc
    let := hc
    apply hns
    change Group.IsSolvable a.ker
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  obtain ⟨hr,hu,m,hm,⟨em⟩⟩ := three_prime_rank_one_residual_suzuki hs h3 h5 hnsC
  let er : solvableResidual C ≃* quotientCentralizerResidual K :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  exact ⟨hr,hu,m,hm,⟨(QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).symm.trans em⟩⟩
/-- The full normalizer of the nonsolvable quotient-centralizer residual is
exactly the original maximal residual normalizer. -/
theorem normalizer_quotientCentralizerResidual_eq (K : Subgroup G)
    (hmax : IsMaximalTwoLocal (normalizer (K : Set G)))
    (hchar : centralizer (pCore 2 (normalizer (K : Set G)) :
      Set (normalizer (K : Set G))) ≤ pCore 2 (normalizer (K : Set G)))
    (hns : ¬ Group.IsSolvable (normalizerQuotientAction K (pCore 2 K)).ker) :
    normalizer (quotientCentralizerResidual K : Set G) = normalizer (K : Set G) := by
  have hn := normalizer_le_normalizer_quotientCentralizerResidual K
  apply le_antisymm ?_ hn
  apply normalizer_le_of_characteristic_two_unique hchar
  · intro M hM hNM
    exact (hmax.eq_of_le hM.1 hNM).symm
  · exact (map_subtype_le _).trans (map_subtype_le _)
  · intro he
    have hr : solvableResidual (quotientCentralizer K) = ⊥ :=
      ((solvableResidual (quotientCentralizer K)).map_eq_bot_iff_of_injective
        (quotientCentralizer K).subtype_injective).mp he
    let : Group.IsSolvable (quotientCentralizer K) := by
      obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := quotientCentralizer K)
      exact ⟨n,hn.trans hr⟩
    apply hns
    let e : (normalizerQuotientAction K (pCore 2 K)).ker ≃* quotientCentralizer K :=
      (normalizerQuotientAction K (pCore 2 K)).ker.equivMapOfInjective
      (normalizer (K : Set G)).subtype (normalizer (K : Set G)).subtype_injective
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · exact hn

/-- A perfect Suzuki cover contained in the linear normalizer centralizes
the actual two-core quotient. -/
theorem suzuki_commutator_le_linear_core {L B : Subgroup G} {n m : ℕ}
    [Group.IsPerfect B] (hm : 0 < m)
    (eB : (B ⧸ pCore 2 B) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hBL : B ≤ normalizer (L : Set G)) : ⁅B,L⁆ ≤ L.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨eL⟩⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let q := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hq : Function.Surjective q := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 B := by
    ext x
    change eB (QuotientGroup.mk' (pCore 2 B) x) = 1 ↔ _
    rw [← eB.map_one, eB.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsSolvable q.ker := by
    rw [hker]
    let := pCore_isNilpotent (p := 2) (G := B)
    infer_instance
  let a := (normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBL)
  have ha := Theory.Suzuki.BinaryLinearActions.perfect_cover_action_trivial hm q hq
    ((MulAut.congr eL).toMonoidHom.comp a)
  have ha' (b : B) : a b = 1 := (MulAut.congr eL).injective
    ((DFunLike.congr_fun ha b).trans (MulAut.congr eL).map_one.symm)
  apply commutator_le.mpr
  intro b hb l hl
  have he := congrArg (fun f : MulAut (L ⧸ pCore 2 L) =>
    f (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)) (ha' ⟨b,hb⟩)
  simp only [a,MonoidHom.comp_apply,normalizerQuotientAction,
    quotientAut_apply_mk,MulAut.one_apply] at he
  have hh := mem_map_of_mem L.subtype (QuotientGroup.eq_iff_div_mem.mp he)
  change (((L.normalizerMonoidHom (inclusion hBL ⟨b,hb⟩)) ⟨l,hl⟩ : L) : G) / l ∈
    L.pCoreIn 2 at hh
  rw [normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv] at hh
  exact hh

/-- The first two assertions of source 5.1.16(2): the genuine Suzuki
residual has normalizer M⁺ and escapes M=N_G(L). -/
theorem nonsolvable_quotientCentralizer_geometry
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    normalizer (quotientCentralizerResidual (residual H) : Set G) =
      normalizer (residual H : Set G) ∧
    ¬ quotientCentralizerResidual (residual H) ≤ normalizer (L : Set G) ∧
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty
      ((quotientCentralizerResidual (residual H) ⧸
        pCore 2 (quotientCentralizerResidual (residual H))) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let N := normalizer (residual H : Set G)
  let M := normalizer (L : Set G)
  let B := quotientCentralizerResidual (residual H)
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hBN : normalizer (B : Set G) = N := normalizer_quotientCentralizerResidual_eq
    (residual H) hmax (h.qtke.evenCharacteristic T N hmax hTN) hns
  obtain ⟨_,_,m,hm,⟨eB⟩⟩ := nonsolvable_quotientCentralizer_residual_suzuki
    (residual H) (h.qtke.twoLocal_sqtk hmax.1) (linear_residual_quotient hm) hns
  refine ⟨hBN,?_,m,hm,⟨eB⟩⟩
  intro hBM
  let C := quotientCentralizer (residual H)
  let er : solvableResidual C ≃* B :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := er.toMonoidHom) er.surjective
  have hc : ⁅B,L⁆ ≤ L.pCoreIn 2 :=
    suzuki_commutator_le_linear_core (by omega) eB h.linear hBM
  let Q := L.pCoreIn 2
  have hQM : Q ≤ M := (pCoreIn_le 2 L).trans L.le_normalizer
  have hMQ : M ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hQT : Q ≤ (T : Subgroup G) := by
    have hcore := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) hQM hMQ
    exact hcore.trans ((pCoreIn_le_sylow M (T.subtype h.sylow_normalizes)).trans_eq
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes]))
  let : Group.IsPerfect (B.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBM).symm.surjective
  let : (Q.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMQ
  have hnQ : Q.subgroupOf M ≤ normalizer (B.subgroupOf M : Set M) := by
    rw [← subgroupOf_normalizer_eq hBM]
    exact comap_mono (hQT.trans (hTN.trans hBN.ge))
  have hcM : ⁅B.subgroupOf M,L.subgroupOf M⁆ ≤ Q.subgroupOf M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hBM,
      map_subgroupOf_eq_of_le L.le_normalizer,map_subgroupOf_eq_of_le hQM]
    exact hc
  have hn := normalizes_perfect_of_commutator_le (B.subgroupOf M)
    (Q.subgroupOf M) (L.subgroupOf M) (isPGroup_pCoreIn 2 L).comap_subtype hnQ hcM
  have hLN : L ≤ N := by
    rw [← subgroupOf_normalizer_eq hBM] at hn
    intro l hl
    exact hBN.le (hn (show (⟨l,L.le_normalizer hl⟩ : M) ∈ L.subgroupOf M from hl))
  have hLstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop,?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hNM := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hLstar).normalizer_unique
    N hmax (sup_le hLN hTN)
  have heL : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl h.sylow_normalizes)
      (le_componentOrbit _ _)
  rw [heL] at hNM
  exact residual_not_le T H M hH.1.1.2 h.sylow_normalizes hH.1.2
    ((residual H).le_normalizer.trans hNM.le)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
