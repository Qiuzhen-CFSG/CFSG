module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.SevenOrder

/-!
# Full-Sylow exclusions for the remaining parabolic common containers

The original diagram residual is a local component normalized by the full
original Sylow. Restricting that Sylow to the common component and mapping
through the literal ambient two-core quotient preserves the intrinsic
SL₃(4) quotient, including its cubic scalar center. The selected parabolic
is never assumed to be an actual H-component.

The M₂₄ local quotient alternatives have incompatible orders. In J₂, a
proper local component generates a proper full-Sylow overgroup, whose order
is prime to seven. In Rudvalis the corresponding overgroup has order prime
to nine. Both contradict the order of the retained SL₃(4) section.

The binary SU₃ cover is also excluded: full-Sylow non-enlargement first
identifies the original residual with the common component and then with
its proper selected parabolic. This argument retains the central cover.
The source application keeps the original pair, both Cartans, the literal
quotient maps, relative normality and strict changed orbit. Rank-two,
Held, J₄, binary SL₃ covers and 3.M₂₂ remain; this is not the final Cartan
normalization theorem.

Source: Aschbacher–Smith A.3.12, 5.1.12 and 5.2.2,
printed pp.47–48,635,648–649, refs/quasithin.pdf. The imported native
Sylow-overgroup certificates retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem sl3_four_card {Q : Type*} [Group Q]
    (h : IsSL Q 3 4) : Nat.card Q = 60480 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
  norm_num

private theorem sl3_four_quasisimple {Q : Type*} [Group Q]
    (h : IsSL Q 3 4) : IsQuasisimple Q := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := h
  exact IsQuasisimple.of_mulEquiv e.symm

private theorem local_sl3_four_not_mathieu
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q)
    (S : Sylow 2 Q) (V : Subgroup Q)
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Q) ≤ normalizer (V : Set Q))
    (hm : IsSL (V ⧸ pCore 2 V) 3 4) (e : Q ≃* Sporadic.Mathieu.M24) : False := by
  have hc := sl3_four_card hm
  have h7 : 7 ∣ Nat.card (V ⧸ pCore 2 V) := by rw [hc]; norm_num
  rcases JankoMathieu.mathieu_local_models e hQ S V hl hn (sl3_four_quasisimple hm) h7 with
    hb | ⟨F,_,_,hF,⟨a⟩⟩ | ha
  · omega
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF,←Nat.card_congr a.toEquiv,hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · obtain ⟨a⟩ := ha
    rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m24_order] at hc
    norm_num at hc

private theorem simple_quasisimple_core {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [IsQuasisimple Q] : pCore 2 Q = ⊥ := by
  have hz : center Q = ⊥ :=
    (inferInstance : (center Q).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp ht))
  exact bot_unique ((IsQuasisimple.pCore_le_center 2).trans_eq hz)

private theorem local_sl3_four_ne_top
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [IsQuasisimple Q]
    {V : Subgroup Q} (hm : IsSL (V ⧸ pCore 2 V) 3 4)
    (hcard : Nat.card Q ≠ 60480) : V ≠ ⊤ := by
  intro he
  subst V
  let a := QuotientGroup.congr _ _ (topEquiv (G := Q)) (pCore_map_iso 2 (topEquiv (G := Q)))
  let b := (QuotientGroup.quotientMulEquivOfEq (simple_quasisimple_core (Q := Q))).trans
    QuotientGroup.quotientBot
  exact hcard ((Nat.card_congr (a.trans b).toEquiv).symm.trans (sl3_four_card hm))

private theorem local_sl3_four_not_jankoTwo
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [IsQuasisimple Q]
    (S : Sylow 2 Q) (V : Subgroup Q)
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hm : IsSL (V ⧸ pCore 2 V) 3 4) (e : Q ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have hproper : V ≠ ⊤ := local_sl3_four_ne_top hm (by
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num)
  have ht : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv (G := Q)).symm⟩).isCComponent
  have hj := local_sup_ne_top_of_ne_top ht S V hl hproper
  let J := V ⊔ (S : Subgroup Q)
  have hd : 7 ∣ Nat.card J := by
    have hc := sl3_four_card hm
    exact (show 7 ∣ Nat.card (V ⧸ pCore 2 V) by rw [hc]; norm_num).trans
      ((card_quotient_dvd_card _).trans (card_dvd_of_le (show V ≤ J from le_sup_left)))
  have hb := Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_not_seven_dvd
    (S.mapSurjective e.surjective) (J.map e.toMonoidHom) (map_mono le_sup_right) (by
      intro hh
      apply hj
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hh)
  rw [card_map_of_injective e.injective] at hb
  exact hb hd

private theorem rudvalis_proper_not_nine
    (hO : pCore 2 Rudvalis.Model = ⊥)
    (S : Sylow 2 Rudvalis.Model) (J : Subgroup Rudvalis.Model)
    (hSJ : (S : Subgroup Rudvalis.Model) ≤ J) (hj : J ≠ ⊤) : ¬ 9 ∣ Nat.card J := by
  obtain ⟨M,hM,hJM⟩ := (eq_top_or_exists_le_coatom J).resolve_left hj
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSJ.trans hJM)))
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  intro hd
  have hdM := hd.trans (card_dvd_of_le hJM)
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hdM
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max4_card hdM
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hdM
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max6_card hdM

private theorem local_sl3_four_not_rudvalis
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [IsQuasisimple Q]
    (S : Sylow 2 Q) (V : Subgroup Q)
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hm : IsSL (V ⧸ pCore 2 V) 3 4) (e : Q ≃* Rudvalis.Model) : False := by
  have hproper : V ≠ ⊤ := local_sl3_four_ne_top hm (by
    rw [Nat.card_congr e.toEquiv,Rudvalis.model_card]
    norm_num)
  have ht : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv (G := Q)).symm⟩).isCComponent
  have hj := local_sup_ne_top_of_ne_top ht S V hl hproper
  let J := V ⊔ (S : Subgroup Q)
  have hd : 9 ∣ Nat.card J := by
    have hc := sl3_four_card hm
    exact (show 9 ∣ Nat.card (V ⧸ pCore 2 V) by rw [hc]; norm_num).trans
      ((card_quotient_dvd_card _).trans (card_dvd_of_le (show V ≤ J from le_sup_left)))
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : IsQuasisimple Rudvalis.Model := IsQuasisimple.of_mulEquiv e
  have hb := rudvalis_proper_not_nine simple_quasisimple_core
    (S.mapSurjective e.surjective) (J.map e.toMonoidHom) (map_mono le_sup_right) (by
      intro hh
      apply hj
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hh)
  rw [card_map_of_injective e.injective] at hb
  exact hb hd


variable {G : Type*} [Group G] [Finite G]

/-- Restrict the original full Sylow to the common component and retain the
intrinsic SL₃(4) quotient through the literal ambient two-core map. -/
theorem original_residual_sl3_local_image
    {T : Sylow 2 G} {H R X I : Subgroup G}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (_hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hm : IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ∃ (S : Sylow 2 Ibar) (V : Subgroup Ibar),
      V ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Ibar) ≤ normalizer (V : Set Ibar) ∧
      IsSL (V ⧸ pCore 2 V) 3 4 := by
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  have hTKN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hTH.trans (le_normalizer_residual H)
  have hKN : (T.subtype (hTH.trans hHX) : Subgroup X) ≤
      normalizer (K.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hKX]
    exact comap_mono hTKN
  obtain ⟨S,_,hl,hSN⟩ := exists_local_sylow_normalizing (T.subtype (hTH.trans hHX))
    (local_restrict hKlocal hKX) hI.subnormal (subgroupOf_mono X hKI) hKN
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := q.subgroupMap (I.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent r.ker := hr.isNilpotent
  let : Group.IsSolvable r.ker := inferInstance
  let V₀ := (K.subgroupOf X).subgroupOf (I.subgroupOf X)
  let V := V₀.map r
  let a : V₀ ≃* pResidual 2 H :=
    ((subgroupOfEquivOfLe (subgroupOf_mono X hKI)).trans (subgroupOfEquivOfLe hKX)).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hrv : IsPGroup 2 (r.subgroupMap V₀).ker := by
    rw [ker_subgroupMap]
    exact hr.comap_subtype
  let b := (r.subgroupMap V₀).quotientPCoreEquivOfSurjective (r.subgroupMap_surjective V₀) hrv
  refine ⟨S.mapSurjective (q.subgroupMap_surjective _),V,
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl r,
    (map_mono hSN).trans (V₀.le_normalizer_map r),?_⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans e)⟩⟩

/-- The original SL₃(4) residual cannot lie in a Mathieu 24, Hall–Janko
or Rudvalis common component. The original full Sylow is restricted to
that component before taking the literal ambient two-core quotient. -/
theorem SelectedSourceModels.parabolic_common_not_three_sporadics
    {T : Sylow 2 G} {L W H R X I : Subgroup G} {n : ℕ}
    (hs : SelectedSourceModels H R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hX : X ∈ Chapter1.H G) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hm : IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hq : IsQuasisimple ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))))
    (hsi : IsSimpleGroup ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ¬ (Nonempty (Ibar ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (Ibar ≃* Sporadic.LeechRelated.J2.Carrier) ∨ Nonempty (Ibar ≃* Rudvalis.Model)) := by
  let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let : IsQuasisimple Ibar := hq
  let : IsSimpleGroup Ibar := hsi
  obtain ⟨S,V,hl,hN,hSL⟩ := original_residual_sl3_local_image hs hn hH.1.1.2 hHX hIX hI hKI hm
  have hQ := Chapter3.sqtk_of_mem_H h.qtke hX
  have hbar := ChapterE.Structure.sqtk_two_quotient hQ (pCore 2 X) pCore_isPGroup
  dsimp only
  intro hm
  rcases hm with he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact local_sl3_four_not_mathieu (hbar.subgroup Ibar) S V hl hN hSL e
  · exact local_sl3_four_not_jankoTwo S V hl hSL e
  · exact local_sl3_four_not_rudvalis S V hl hSL e

private theorem su3_of_equiv {Y Z : Type*} [Group Y] [Group Z] {f : ℕ}
    (h : IsSU Z 3 (2^f)) (a : Y ≃* Z) : IsSU Y 3 (2^f) := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨a.trans e⟩⟩

private theorem eq_of_binary_su3_quotient
    {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) {V C : Subgroup Y}
    (hl : V ∈ ChapterA.Section03.localCComponents S) (hC : C.IsCComponent) (hVC : V ≤ C)
    {f : ℕ} (hf : 0 < f) (hm : IsSU (C ⧸ pCore 2 C) 3 (2^f)) : V = C := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have he := eq_of_binary_su3_containing_component
    (S.mapSurjective (QuotientGroup.mk'_surjective _))
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    (hC.map_quotient _) (map_mono hVC) hf
    (su3_of_equiv hm (cComponentTwoCoreQuotientEquiv hC).symm)
  exact local_cComponent_eq_of_map_eq hl hC hVC q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S) he

/-- A binary special-unitary common cover cannot contain the original
diagram residual and its proper selected parabolic. Both applications
use actual full Sylow restrictions, and retain the cubic center. -/
theorem LocalData.parabolic_common_not_binary_su3
    {T : Sylow 2 G} {L H A B D R X I : Subgroup G} {p f : ℕ}
    (d : LocalData T L H B D R) (hs : SelectedSourceModels H R)
    (hTH : (T : Subgroup G) ≤ H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hf : 0 < f) :
    ¬ IsSU ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 3 (2^f) := by
  intro hm
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let eI := (cComponentTwoCoreQuotientEquiv hI).symm.trans
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hIX)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hIX)))
  have heX : K.subgroupOf X = I.subgroupOf X :=
    eq_of_binary_su3_quotient (T.subtype (hTH.trans hHX))
      (local_restrict hKlocal hKX) hI (subgroupOf_mono X hKI) hf
      (su3_of_equiv hm (cComponentTwoCoreQuotientEquiv hI))
  have he : K = I := by
    simpa only [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hIX] using
      congrArg (map X.subtype) heX
  have hb : IsSU (K ⧸ pCore 2 K) 3 (2^f) := by
    rw [he]
    exact su3_of_equiv hm eI.symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [K,subgroupOf_self] using
      (hs.residual_component_of_not_right hn).subgroupOf_of_le (le_refl K) hKH
  obtain ⟨S,_,hR⟩ := d.right_local_in_residual hTH
  let eTop := QuotientGroup.congr _ _ (topEquiv (G := K))
    (pCore_map_iso 2 (topEquiv (G := K)))
  have heR : R.subgroupOf K = ⊤ :=
    eq_of_binary_su3_quotient S hR htop le_top hf (su3_of_equiv hb eTop)
  exact (d.right_lt_residual hTH c hd hz).not_ge (subgroupOf_eq_top.mp heR)

/-- The same source pair excludes M₂₄, J₂ and Rudvalis using its full
original residual Sylow, and excludes binary SU₃ covers. The remaining
simple finite rows are Held and J₄; the rank-two, binary SL₃ and 3.M₂₂
rows remain explicit. -/
theorem source_prime_pair_parabolic_local_containers
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He) ∨
                    (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∧
                      Nonempty (Ibar ≃* Janko4.Model)))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    ((∃ f : ℕ, 1 ≤ f ∧
                      (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f)) ∨
                      (IsM22Cover Ibar ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                        IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_finite_containers h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with ⟨hsi,hm⟩ | hm
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hrank | he | ⟨hfour,hSL,name,hname,he⟩
    · exact .inl hrank
    · exact .inr (.inl he)
    · have hnot := hs.parabolic_common_not_three_sporadics h hH hn
        (d.common_normal_overgroup h hH c hd hz).1 le_sup_right hIX hI hKI hSL hquasi hsi
      rcases hname with hname | hname | hname | hname
      · subst name
        exact (hnot (.inl he)).elim
      · subst name
        exact (hnot (.inr (.inl he))).elim
      · subst name
        exact .inr (.inr ⟨hfour,hSL,he⟩)
      · subst name
        exact (hnot (.inr (.inr he))).elim
  · obtain ⟨hc,hm⟩ := hm
    refine .inr ⟨hc,?_⟩
    rcases hm with ⟨unitary,f,hf,hmod,hmodel⟩ | hm
    · cases unitary with
      | false => exact .inl ⟨f,hf,hmod,hmodel⟩
      | true => exact (d.parabolic_common_not_binary_su3 hs hH.1.1.2 c hd hz hn
          le_sup_right hIX hI hKI (by omega : 0 < f) hmodel).elim
    · exact .inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
