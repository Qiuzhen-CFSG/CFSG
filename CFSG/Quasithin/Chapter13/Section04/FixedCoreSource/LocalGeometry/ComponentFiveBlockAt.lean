module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFiveAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryBaumannAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFiveExclusion

/-!
# Excluding the ordinary-original A₅ row at the same G,T

The original augmentation point radical has the same two-rank as O₂(LT).
The selected A₅ point calculation identifies its Thompson and Baumann
subgroups with those of O₂(KT), forcing the original augmentation component
to be short. Transport the resulting two-chief-factor budget through the
literal reciprocal residual to recognize K as an A₅ block. Every maximal
elementary subgroup of O₂(LT) is then normalized by K. Maximal-local
uniqueness places K in N_G(L), contradicting escape.

This specializes Nonsolvable/ComponentFiveBaumann, ComponentFiveBlock and
ComponentFiveExclusion to Structural1222At. The independent natural
LargeDistanceInput is retained; no shortness, chief count or block conclusion
is added as a premise. ComponentCoveredFiveAt combines both original rows.
Source: Aschbacher--Smith 13.2.2(6--7), 13.4.10(1), printed pp.877--878,908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The original five-space gives the full two-rank and Thompson containment on O₂(L₁T). -/
theorem ordinary_augmentation_point_rank_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    ChapterB.twoRank R = ChapterB.twoRank ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      V ≤ elementaryAbelianMaxJ R := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hXV : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi : U := eu.symm z
  obtain ⟨q,hq,hqL,him,hker⟩ := exists_core_product_permutation_at D m h structural eL
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := by
    exact hq x (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    rw [←him]
    exact (L.subgroupOf X).map_le_range q
  have hz : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro hz
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at hz
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using hz
  have hh := ChapterB.Offenders.SixCorePoint.pointRadical_rank_and_module U q e he hker hY zi hz
  let C : Subgroup X := centralizer ({zi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
    · rintro ⟨hx,hz⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr ?_,rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hz)
  have hRm : (C.pCoreIn 2).map X.subtype =
      (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  refine ⟨?_,?_⟩
  · rw [←hRm,ChapterB.twoRank_map_injective X.subtype X.subtype_injective]
    change ChapterB.twoRank (C.pCoreIn 2) = ChapterB.twoRank ((pCore 2 X).map X.subtype)
    rw [ChapterB.twoRank_map_injective X.subtype X.subtype_injective]
    exact hh.1.symm
  · have hhV := map_mono (f := X.subtype) hh.2
    rw [map_subgroupOf_eq_of_le hVX,←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm] at hhV
    exact hhV

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])

/-- The literal original point radical has the Thompson and Baumann subgroups of O₂(KT). -/
theorem ordinary_five_original_baumann_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,qK,e,he⟩ := component_five_marking_at h₀ h structural D m
    h1332 modules hzT hz1 hKz hHN hKM hfK eK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  let Ki := K.subgroupOf X
  let Ui := U.subgroupOf X
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let : Ui.Normal := hred.normal
  let : IsElementaryAbelian 2 Ui := hred.elementary
  let q0 := qK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let q := q0.comp ek.toMonoidHom
  have hq : Function.Surjective q :=
    (qK.surjective.comp (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hk : q.ker = pCore 2 Ki := by
    change q0.ker.comap ek.toMonoidHom = _
    have hq0 : q0.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ qK.injective,QuotientGroup.ker_mk']
    rw [hq0]
    exact ek.toMonoidHom.comap_pCore_of_ker_isPGroup ek.surjective
      (IsPGroup.ker_isPGroup_of_injective ek.injective)
  let ei := eu.trans e
  have hei (k : Ki) (u : Ui) : (ei (MulAut.conjNormal k.val u)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q k).val (ei u).toAdd := by
    exact he (ek k) (eu u)
  have hquot : IsPGroup 2 (X ⧸ Ki) := by
    apply isPGroup_quotient_of_sup_eq_top Ki ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  obtain ⟨_,_,w,hw,hTw,hPar⟩ := ordinary_five_component_residuals_at h₀ h structural D m
    h1332 modules eL z hzT hzL hKz hHN hKM hfK eK
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  let Si := S.mapSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  have hSi : (Si : Subgroup Ki).map Ki.subtype ≤ centralizer ({wi.val} : Set X) := by
    rintro x ⟨a,ha,rfl⟩
    obtain ⟨k,hk,hka⟩ := (show a ∈ (S : Subgroup K).map ek.symm.toMonoidHom from ha)
    rw [←hka]
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hk))))
  have hb := ChapterB.AlternatingFivePoint.overgroup_point_baumann Ki Ui q hq hk ei hei hquot
    (le_centralizer_iff.mp hred.le_centralizer_pCore) wi hwi Si hSi
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [hPar]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = (ChapterB.baumann (pCore 2 X)).map X.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective X.subtype X.subtype_injective,
    baumann_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hm
  have hj := congrArg (fun A : Subgroup X => A.map X.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype =
    (elementaryAbelianMaxJ (pCore 2 X)).map X.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hj
  change ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2) =
    ChapterB.baumann (X.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  intro hbound
  exact hKM ((show K ≤ X from le_sup_left).trans ((X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      ((normalizer_le_normalizer_baumann (X.pCoreIn 2)).trans hbound)))

/-- The selected A₅ row forces the original augmentation component to be short. -/
theorem ordinary_five_short_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : ChapterC.IsShort L := by
  have hescape := (ordinary_five_original_baumann_at h₀ h structural D m
    h1332 modules eL z hzT hzL hKz hHN hKM hfK eK).2.2
  exact (ordinary_augmentation_baumann_alternative_of_largeDistance_at
    hl h structural D m eL z hzT hzL).resolve_left hescape

/-- Recognize the actual selected A₅ block from the original two-chief-factor budget. -/
theorem ordinary_five_block_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ChapterC.IsAlternatingBlock K 5 ∧
      (ChapterC.blockU K).map K.subtype =
        ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by

  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hshort := ordinary_five_short_of_largeDistance_at hl h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,qK,e,he⟩ := component_five_marking_at h₀ h structural D m h1332 modules
    hzT hz1 hKz hHN hKM hfK eK
  have hUK : U ≤ K := DK.le_component
  let Ui := U.subgroupOf K
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer DK.normalizes
  let := DK.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.comap_of_injective K.subtype K.subtype_injective U
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUK
  let ei := eu.trans e
  let q := qK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := qK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ qK.injective,QuotientGroup.ker_mk']
  have hei (k : K) (v : Ui) : (ei (MulAut.conjNormal k v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q k).val (ei v).toAdd := by
    exact he k (eu v)
  obtain ⟨w,hw,hTw,hX⟩ := component_fixed_generator_point_overgroup_at h₀ h structural m
    hzT hz1 hKz hTK hKM
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  have hSw : (S : Subgroup K) ≤ centralizer ({wi.val} : Set K) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hx))))
  let C := centralizer ({wi.val} : Set K)
  have hCm : C.map K.subtype = K ⊓ centralizer ({m.constant.val} : Set G) := by
    ext k
    constructor
    · rintro ⟨a,ha,rfl⟩
      have hc : a.val ∈ centralizer ({w.val} : Set G) :=
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
      exact ⟨a.property,(hX.ge ⟨mem_sup_left a.property,hc⟩).2⟩
    · rintro ⟨hk,hc⟩
      have hwc := (hX.le ⟨mem_sup_left hk,hc⟩).2
      exact ⟨⟨k,hk⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hwc)),rfl⟩
  have hres := (ordinary_five_component_residuals_at h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK).2.1
  let R := (primeToResidual 3 C).map C.subtype
  have hRm : R.map K.subtype = Solvable.firstCentralizerResidual L z.val := by
    change ((primeToResidual 3 C).map C.subtype).map K.subtype = _
    rw [map_embedded_primeToResidual_of_hom,hCm,←Solvable.firstCentralizerResidual_eq,hres]
  let er : primeToResidual 3 C ≃* Solvable.firstCentralizerResidual L z.val :=
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((R.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hRm))
  have hcount : ∀ s : ChiefSeries (primeToResidual 3 C),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2 := by
    intro s hs0 hs1
    have hc := s.mapActor_complete er hs0 hs1
    have hh := core_firstResidual_chief_count_le_two D m hshort eL z hzL
      (s.mapActor er) hc.1 hc.2
    rwa [s.mapActor_noncentralTwoCount] at hh
  have hU : ⁅Ui,(⊤ : Subgroup K)⁆ = Ui := by
    apply map_injective K.subtype_injective
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hUK]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hf := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK
  have hb : ChapterC.blockU K = Ui :=
    ChapterB.AlternatingFivePoint.core_commutator_of_point_chief_budget Ui q hq hk ei hei
      hf.2.1.2.1 hU wi hwi S hSw hcount
  have hbmap : (ChapterC.blockU K).map K.subtype = U := by
    rw [hb,map_subgroupOf_eq_of_le hUK]
  refine ⟨?_,hbmap⟩
  let eb := (MulEquiv.subgroupCongr hb).trans ei
  apply Section03.Noncentrality.OrdinaryBlockRecognition.alternatingBlock_of_layer qK eb ?_
    hf.2.1.2.1 hf.2.1.2.2
  intro k v
  exact hei k ((MulEquiv.subgroupCongr hb) v)

/-- Exclude the selected A₅ component when the original component has ordinary A₆ quotient. -/
theorem ordinary_five_excluded_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : False := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  let QK := X.pCoreIn 2
  let Y := L ⊔ (T : Subgroup G)
  let QL := Y.pCoreIn 2
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨hb,_⟩ := ordinary_five_block_of_largeDistance_at hl h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,_,_,_⟩ := component_five_marking_at h₀ h structural D m h1332 modules
    hzT hz1 hKz hHN hKM hfK eK
  let := DK.elementary
  have hJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ QK :=
    (ordinary_five_original_baumann_at h₀ h structural D m h1332 modules
      eL z hzT hzL hKz hHN hKM hfK eK).1
  have hr : ChapterB.twoRank R = ChapterB.twoRank QL :=
    (ordinary_augmentation_point_rank_at h structural D m eL z hzT hzL).1
  have hPY : P ≤ Y := sup_le
    ((Solvable.firstCentralizerResidual_le L z.val).trans inf_le_left |>.trans le_sup_left)
    le_sup_right
  have hQP : QL ≤ P := by
    dsimp only [P]
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    exact le_inf (pCoreIn_le 2 Y)
      (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
  have hQR : QL ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQP
    (hPY.trans (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))
  obtain ⟨_,_,w,_,_,hP⟩ := ordinary_five_component_residuals_at h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  have hPX : P ≤ X := hP.le.trans inf_le_left
  have hKP : QK ≤ P := by
    dsimp only [P]
    rw [hP]
    exact le_inf (pCoreIn_le 2 X)
      (DK.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr w.property)))
  have hKR : QK ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hKP
    (hPX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hUR : U ≤ R := DK.le_core.trans hKR
  have hKT : QK ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] using
      pCoreIn_le_sylow X (T.subtype le_sup_right)
  have hJK : elementaryAbelianMaxJ QK ≤ QK := sSup_le fun _ hA => hA.1
  have hnormal (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups QL) :
      K ≤ normalizer (A : Set G) := by
    have hAR : A ∈ elementaryAbelianMaxSubgroups R := by
      refine ⟨hA.1.trans hQR,hA.2.1,?_⟩
      intro B hBR hB
      have hcard : Nat.card A = elementaryAbelianMaxOrder R := by
        rw [card_eq_elementaryAbelianMaxOrder QL A hA,
          ChapterB.maxOrder_eq_two_pow_rank,ChapterB.maxOrder_eq_two_pow_rank,hr]
      rw [hcard]
      obtain ⟨B₀,hB₀⟩ := elementaryAbelianMaxSubgroups_nonempty R
      exact (hB₀.2.2 B hBR hB).trans_eq (card_eq_elementaryAbelianMaxOrder R B₀ hB₀)
    have hAK : A ≤ QK := (le_sSup hAR).trans (hJ.le.trans hJK)
    have hUA : U ≤ A := maxElementary_contains_elementary_centralizer R A U hAR hUR
      (le_centralizer_iff.mp (hAK.trans DK.core_centralizes))
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (le_inf (hAK.trans hKT) (hAK.trans DK.core_centralizes)) le_rfl).trans
      ((Solvable.sylow_module_centralizer_commutator_le_chosen DK hb.2.1).trans hUA)
  have hKJ : K ≤ normalizer (elementaryAbelianMaxJ QL : Set G) := by
    change K ≤ normalizer ((sSup (elementaryAbelianMaxSubgroups QL) : Subgroup G) : Set G)
    rw [sSup_eq_iSup']
    exact (le_iInf fun A : elementaryAbelianMaxSubgroups QL => hnormal A A.property).trans
      (iInf_normalizer_le_normalizer_iSup _)
  have hJQ : elementaryAbelianMaxJ QL ≤ QL := sSup_le fun _ hA => hA.1
  have hYN : Y ≤ normalizer (elementaryAbelianMaxJ QL : Set G) :=
    (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ QL)
  let := D.elementary
  have hVJ : V ≤ elementaryAbelianMaxJ QL := by
    have hv := elementary_centralizer_maxJ_le_omegaCenter QL V D.le_core
      ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hJQ))
    intro v hvV
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hv hvV)).1
  have hne : elementaryAbelianMaxJ QL ≠ ⊥ := fun hh => D.ne_bot (eq_bot_iff.mpr (hh ▸ hVJ))
  have hbound := normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 Y).to_le hJQ) hne hYN
  exact hKM (hKJ.trans hbound)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
