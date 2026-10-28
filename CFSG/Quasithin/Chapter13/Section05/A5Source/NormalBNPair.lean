module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointCentralizer
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.Amalgam.SylowRigidity
/-!
# The original normal A₅ pair and faithful local amalgam

The selected pair I=⟨V,Vʳ⟩ has its original quaternion two-core, is normal
in H, and has quotient S₃. Keeping that same choice, Sylow restriction gives
B_I=T∩I. The original five-letter action identifies B_L=C_L(V₁), so the
common Borel is L₁T and the two parabolics are exactly H and LT.

The source generated-core and characteristic-two facts establish every
clause of the genuine F.1.1 hypothesis for (I,L,T). F.1.3(6) then gives
H∩LT=L₁T. Faithfulness follows directly: a subgroup normal in both endpoints
and contained in L₁T centralizes the L-span of V₁, hence V. It therefore
lies in V=C_G(V) and in the trivial two-core of ⟨H,LT⟩.

These are the literal local inputs in 13.5.17. The compatible unitary-amalgam
classification in F.1.12 and the final ambient model recognition remain
separate; neither is assumed or asserted here.

Source: Aschbacher–Smith, 13.5.17, printed p.922, and F.1.1–9,
printed pp.259–262 of the combined 1 March 2004 manuscript.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

omit hn in
/-- The actual quaternion-core identity suffices to recover the S₃ quotient
for any selected original pair, without choosing a second conjugator. -/
theorem normal_pair_quotient_of_core (r : G) (hrH : r ∈ H)
    (hc : (V ⊔ V.map (MulAut.conj r).toMonoidHom).pCoreIn 2 = Source.UH H V₃) :
    Nonempty (((V ⊔ V.map (MulAut.conj r).toMonoidHom : Subgroup G) ⧸
      pCore 2 (V ⊔ V.map (MulAut.conj r).toMonoidHom : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  have hIH : I ≤ H := sup_le hf.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (hf.V_le_H hv)) (H.inv_mem hrH))
  have hnot : ¬ IsPGroup 2 (Source.starImage H I) := by
    intro hp
    let π := QuotientGroup.mk' (pCore 2 H)
    have hk : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have hpre := hp.comap_of_ker_isPGroup π hk
    have hIP : IsPGroup 2 I := by
      have h := hpre.to_le (le_comap_map π (I.subgroupOf H))
      exact h.of_surjective (subgroupOfEquivOfLe hIH).toMonoidHom
        (subgroupOfEquivOfLe hIH).surjective
    have hIcore : I ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes hIP le_rfl I.le_normalizer
    have hv : V ≤ Source.QH H := le_sup_left.trans (hIcore.trans (hc.le.trans hf.UH_le_QH))
    exact hU (hf.UH_elementary_of_V_le_QH hv).toIsMulCommutative
  exact normal_pair_quotient_symmetricThree d hA312 hH r hrH
    (hf.pair_star_symmetricThree d.third_index d.module_card
      (fun _ hg hi => source13_5_13_one d hA312 hH hU hg hi)
      (source_seed_centralizer_bound d hA312) r hrH hnot)

omit d hA312 hH hU hn [IsElementaryAbelian 2 V] in
private theorem sylow_intersection {A : Subgroup G} (hTA : (T : Subgroup G) ≤ A)
    {I : Subgroup G} (hIA : I ≤ A) (hAI : A ≤ normalizer (I : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I := by
  let S := T.subtype hTA
  let : (I.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hIA).mpr hAI
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal (I.subgroupOf A)
  let e := subgroupOfEquivOfLe hIA
  let Q : Sylow 2 I := R.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q,?_⟩
  change ((R : Subgroup (I.subgroupOf A)).map e.toMonoidHom).map I.subtype = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨hz,z.property⟩
  · rintro ⟨hxT,hxI⟩
    exact ⟨⟨x,hxI⟩,⟨⟨⟨x,hIA hxI⟩,hxI⟩,hxT,rfl⟩,rfl⟩

/-- One original pair simultaneously supplies normality, generation,
its rank-one quotient and the self-normalizing Sylow intersection. -/
theorem source_normal_pair_rank_one_normal :
    ∃ r ∈ H, orderOf r = 3 ∧
      let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
      I.pCoreIn 2 = Source.UH H V₃ ∧
      H = residualCentralizer L V₁ ⊔ I ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (I : Set G) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      ChapterF.Source.IsRankOneModel (I ⧸ pCore 2 I) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I ∧
      ChapterF.Source.borel I (T : Subgroup G) = (T : Subgroup G) ⊓ I := by
  obtain ⟨r,hrH,hr,hcore,hgen,hnorm,_⟩ := source_normal_pair_normal d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  have hIH : I ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨e⟩ := normal_pair_quotient_of_core d hA312 hH hU r hrH hcore
  have hSyl := sylow_intersection hTH hIH hnorm
  have hb := ChapterF.Source.borel_eq_of_cubic_local_sylow I ((T : Subgroup G) ⊓ I) hSyl e
  have hb' : ChapterF.Source.borel I (T : Subgroup G) = (T : Subgroup G) ⊓ I := by
    simpa only [ChapterF.Source.borel,inf_assoc,inf_idem] using hb
  refine ⟨r,hrH,hr,hcore,hgen,hnorm,⟨e⟩,?_,hSyl,hb'⟩
  apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩

/-- All six original F.1.1 clauses for a single chosen pair, together with
the literal parabolics and common Borel used in 13.5.17. -/
theorem source_normal_pair_F11 :
    ∃ r ∈ H, orderOf r = 3 ∧
      let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
      ChapterF.Source.HypothesisF11 ![I,L] (T : Subgroup G) ∧
      ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 0 = H ∧
      ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 1 = L ⊔ (T : Subgroup G) ∧
      ChapterF.Source.commonBorel ![I,L] (T : Subgroup G) =
        residualCentralizer L V₁ ⊔ (T : Subgroup G) ∧
      ChapterF.Source.borel I (T : Subgroup G) = (T : Subgroup G) ⊓ I := by
  have hB := d.borel_sup_sylow_eq_residual_sup_sylow
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨r,hrH,hr,hcore,hgen,hnorm,hIq,hIr,hIS,hIb⟩ :=
    source_normal_pair_rank_one_normal d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  change H = residualCentralizer L V₁ ⊔ I ⊔ (T : Subgroup G) at hgen
  change H ≤ normalizer (I : Set G) at hnorm
  change ChapterF.Source.borel I (T : Subgroup G) = (T : Subgroup G) ⊓ I at hIb
  have hIH : I ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_left
  have hBL : ChapterF.Source.borel L (T : Subgroup G) ≤ H :=
    (le_sup_left.trans hB.le).trans hf.local_le
  obtain ⟨hB',h0,h1⟩ := d.source_pair_borel_parabolics hIb hgen
  have hMchar : generalizedFitting (L ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    have hne : (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≠ ⊥ := by
      rw [normal_local_core_eq_module d hA312 hH hU hn]
      intro he
      have hc := d.module_card
      rw [he,card_bot] at hc
      contradiction
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (d.hypothesis.qtke.evenCharacteristic T)
          ⟨hne,(show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)⟩))
  have hLS : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ L) L := d.local_sylow
  have hF : ChapterF.Source.HypothesisF11 ![I,L] (T : Subgroup G) := by
    refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,?_⟩
    · intro i
      fin_cases i
      · exact hf.T_le_H.trans hnorm
      · exact d.normalizes_L
    · intro i
      fin_cases i
      · exact hIS
      · exact hLS
    · intro i
      fin_cases i
      · exact hIr
      · exact d.quotient_rankOneModel
    · intro i
      fin_cases i
      · exact hBL.trans hnorm
      · change ChapterF.Source.borel I (T : Subgroup G) ≤ normalizer (L : Set G)
        exact hIb.le.trans (inf_le_left.trans d.normalizes_L)
    · change pCore 2 (I ⊔ L ⊔ (T : Subgroup G) : Subgroup G) = ⊥
      have he : I ⊔ L ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊔ H := by
        apply le_antisymm
        · exact sup_le (sup_le (hIH.trans le_sup_right) (le_sup_left.trans le_sup_left))
            (le_sup_right.trans le_sup_left)
        · refine sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) ?_
          rw [hgen]
          exact sup_le (sup_le
            (((map_subtype_le _).trans inf_le_left).trans (le_sup_right.trans le_sup_left))
            (le_sup_left.trans le_sup_left)) le_sup_right
      rw [he]
      exact hf.generated_core
    · intro i
      fin_cases i
      · change generalizedFitting (ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 0) =
            pCore 2 (ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 0)
        rw [h0]; exact hf.characteristic_H
      · change generalizedFitting (ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 1) =
            pCore 2 (ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 1)
        rw [h1]; exact hMchar
  exact ⟨r,hrH,hr,hF,h0,h1,hB',hIb⟩

/-- The actual normal A₅ inclusion amalgam is faithful: a common normal
subgroup centralizes the L-span of the original point and lies in V. -/
theorem source_normal_amalgam_faithful :
    RankTwoAmalgam.Faithful
      (RankTwoAmalgam.ofSubgroups H
        (residualCentralizer L V₁ ⊔ (T : Subgroup G)) (L ⊔ (T : Subgroup G))
        hH.1.2 (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl)) := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let M := L ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hH.1.2
  have hBM : B ≤ M := sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  intro N hNH hNM
  let K := N.map B.subtype
  have hKB : K ≤ B := map_subtype_le _
  have heH : K.subgroupOf H = N.map (inclusion hBH) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (hKB.trans hBH), map_map]
    rfl
  have heM : K.subgroupOf M = N.map (inclusion hBM) := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (hKB.trans hBM), map_map]
    rfl
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hKB.trans hBH)).mp (heH ▸ hNH)
  have hMK : M ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hKB.trans hBM)).mp (heM ▸ hNM)
  have h1 : V₁ ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp (hKB.trans (hBH.trans hH.2.1))
  have hL : L ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (le_sup_left.trans hMK).trans (normalizer_le_normalizer_centralizer K)
  have hV : K ≤ V := by
    have hVK : V ≤ centralizer (K : Set G) := by
      rw [←d.line_span_eq]
      exact conjugateSpanBy_le h1 hL
    exact (le_centralizer_iff.mp hVK).trans (normal_maximal_core_eq_module d hA312 hH hU hn).2.2.le
  have hcore : K ≤ (M ⊔ H : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 V).to_le hV)
      ((hKB.trans hBM).trans le_sup_left) (sup_le hMK hHK)
  have hk : K = ⊥ := by
    apply bot_unique
    change K ≤ (pCore 2 (D.LT ⊔ D.H : Subgroup G)).map (D.LT ⊔ D.H).subtype at hcore
    rw [hf.generated_core,Subgroup.map_bot] at hcore
    exact hcore
  apply map_injective B.subtype_injective
  rw [Subgroup.map_bot]
  exact hk

/-- The original source parabolics meet in exactly L₁T. This applies F.1.3(6)
to the just-constructed F.1.1 datum, retaining its two inclusion maps. -/
theorem normal_local_intersection :
    H ⊓ (L ⊔ (T : Subgroup G)) = residualCentralizer L V₁ ⊔ (T : Subgroup G) := by
  obtain ⟨r,_,_,hF,h0,h1,hB,_⟩ := source_normal_pair_F11 d hA312 hH hU hn
  have he := ChapterF.Source.lemma_F_1_3_6 hF
  rwa [h0,h1,hB] at he
end CFSG.Quasithin.Chapter13.Section05.A5Source
