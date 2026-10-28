module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineContainment
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.CubicKernelResidual

/-!
# The moved cubic kernel line in the original normal nine-lift

The selected normal nine-lift lies in M = N_G(L). Its literal action on
L/O₂(L) is nontrivial by ambient normalizer control. Since Aut(L₃(2)) has
order 336, the action kernel has cubic image modulo the entire two-core.
Its two-residual C is T-invariant and centralizes L modulo O₂(L), so
N_G(C) lies in M and the escaping local J cannot normalize C.

The star map has kernel exactly O₂(C) on this lift. If the three-core
normalized its cubic image, the Sylow supplement and normalization by the
whole star-map kernel would lift normality to J, a contradiction. Hence
the actual three-core moves this cubic line, and in particular is nonabelian.
The last theorem applies this to the original minimal solvable witness,
preserving its normal nine-lift or Heisenberg center marking.

This supplies the moving-line input in the elementary-nine branch of
14.5.20. The cyclic-nine enlargement, terminal solvable exclusions and the
four final inputs through 14.7.52 remain to be proved.
Source: Aschbacher–Smith, 14.5.20, printed p.1019; 14.7.9 and
14.7.27–29, pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual quotient-centralizer residual of the normal nine-lift is
cubic and T-invariant, and its full ambient normalizer lies in M. -/
theorem local_solvable_nine_centralizing_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    let B := Y.map J.subtype
    let D := pCoreActionKernelIn 2 L B
    let C := (pResidual 2 D).map D.subtype
    C ≤ B ∧ IsPPerfect 2 C ∧ (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      Nat.card (C ⧸ pCore 2 C) = 3 ∧
      ⁅L,C⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C : Set G) ≤ normalizer (L : Set G) ∧
      ¬ J ≤ normalizer (C : Set G) := by
  let M := normalizer (L : Set G)
  let B := Y.map J.subtype
  let D := pCoreActionKernelIn 2 L B
  let C := (pResidual 2 D).map D.subtype
  have hBM : B ≤ M := local_solvable_nine_lift_containment
    h hab structural previous faithful J hJ hs Y hYp hAY e
  have hBp : IsPPerfect 2 B := hYp.of_surjective (J.subtype.subgroupMap Y)
    (J.subtype.subgroupMap_surjective Y)
  let eB := equivMapOfInjective Y J.subtype J.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 Y) (pCore 2 B) eB (pCore_map_iso 2 eB)
  have h9 : Nat.card (B ⧸ pCore 2 B) = 9 := by
    rw [←Nat.card_congr eQ.toEquiv,Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hYn : Y ≠ ⊥ := by
    intro hz
    have hc : Nat.card (Y ⧸ pCore 2 Y) = 9 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod]
      norm_num [Nat.card_zmod]
    rw [hz] at hc
    have ho : Nat.card ((⊥ : Subgroup J) ⧸ pCore 2 (⊥ : Subgroup J)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1,fun _ => Subsingleton.elim _ _⟩
    omega
  let f : B →* MulAut (L ⧸ pCore 2 L) :=
    (pCoreNormalizerAction 2 L).comp (inclusion hBM)
  have hfn : f ≠ 1 := by
    intro hf
    obtain ⟨x,hx⟩ := local_normal_twoPerfect_quotient_action_nontrivial
      h structural J hJ Y hYp hYn hBM
    exact hx (DFunLike.congr_fun hf x)
  let := h.chosen.elementary
  let eL := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  have hcAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    rw [Nat.card_congr (MulAut.congr (eL.trans Matrix.PSL3Two.equiv)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  obtain ⟨hCn,hCp,hCf,hm,hc⟩ := f.cubic_kernel_residual hBp hfn h9
    (by rw [hcAut]; decide)
  let C₀ := (pResidual 2 f.ker).map f.ker.subtype
  let : C₀.Normal := hCn
  have hD : D = f.ker.map B.subtype := pCoreActionKernelIn_eq_map_ker 2 L B hBM
  have hC : C₀.map B.subtype = C := by
    rw [show C₀ = (pResidual 2 f.ker).map f.ker.subtype from rfl,map_embedded_pResidual,←hD]
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 := by
    let ee := (equivMapOfInjective C₀ B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr hC)
    exact (Nat.card_congr (QuotientGroup.congr _ _ ee (pCore_map_iso 2 ee)).toEquiv).symm.trans hc
  have hCB : C ≤ B := (map_subtype_le _).trans inf_le_left
  have hJB : J ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hMD : M ≤ normalizer
      (((pCoreNormalizerAction 2 L).ker).map M.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCoreNormalizerAction 2 L).ker.le_normalizer_map M.subtype
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf ((F.sylow_le_of_mem_Hz hJ).trans hJB)
      ((h.sylow_normalizes structural).trans hMD)).trans inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    hTD.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  have hcomm : ⁅L,C⁆ ≤ L.pCoreIn 2 :=
    (commutator_mono le_rfl (map_subtype_le _)).trans (pCoreActionKernelIn_commutator 2 L B)
  have hCne : C ≠ ⊥ := by
    intro hz
    rw [hz] at hcC
    have ho : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1,fun _ => Subsingleton.elim _ _⟩
    omega
  have hbound := local_twoPerfect_core_commutator_normalizer h structural J hJ C
    (hCB.trans (map_subtype_le Y)) (isPPerfect_embedded_pResidual 2 D) hCne hTC hcomm
  exact ⟨hCB,isPPerfect_embedded_pResidual 2 D,hTC,hcC,hcomm,hbound,
    fun hj => hJ.2.2 (hj.trans hbound)⟩


/-- The cubic kernel lift has its intrinsic two-core as the exact star-map
kernel, and the actual three-core moves its cubic image. -/
theorem local_solvable_nine_centralizing_line_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ∃ C : Subgroup J, C ≤ Y ∧ IsPPerfect 2 C ∧
      (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp C.subtype).ker = pCore 2 C ∧
      Nat.card (C.map (QuotientGroup.mk' (pCore 2 J))) = 3 ∧
      ⁅L,C.map J.subtype⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C.map J.subtype : Set G) ≤ normalizer (L : Set G) ∧
      ¬ pCore 3 (HStar J) ≤ normalizer
        (C.map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) := by
  let D := pCoreActionKernelIn 2 L (Y.map J.subtype)
  let C₀ := (pResidual 2 D).map D.subtype
  obtain ⟨hCB,hCp,hTC,hc,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_lift h hab structural previous faithful J hJ hs Y hYp hAY e
  have hCJ : C₀ ≤ J := hCB.trans (map_subtype_le Y)
  let C := C₀.subgroupOf J
  have hmap : C.map J.subtype = C₀ := map_subgroupOf_eq_of_le hCJ
  have hCY : C ≤ Y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hmap]
    exact hCB
  let eC := subgroupOfEquivOfLe hCJ
  have hp : IsPPerfect 2 C := hCp.of_surjective eC.symm.toMonoidHom eC.symm.surjective
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).toEquiv).trans hc
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp C.subtype
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkf : IsPGroup 2 f.ker := hkq.comap_of_injective _ C.subtype_injective
  have h3Y : IsPGroup 3 (Y.map q) := by
    let eY := (coreQuotientEquivImage 2 Y).symm.trans e
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr eY.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hfr : f.range = C.map q := by rw [MonoidHom.range_comp,range_subtype]
  have h3 : IsPGroup 3 f.range := hfr.symm ▸ h3Y.to_le (map_mono hCY)
  have h2 : pCore 2 f.range = ⊥ :=
    bot_unique ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (h3.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hk : f.ker = pCore 2 C := f.ker_eq_pCore_of_range_core_eq_bot 2 hkf h2
  have hcc : Nat.card (C.map q) = 3 := by
    rw [←hfr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hk]
    exact hcC
  have hTC' : (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) := hmap.symm ▸ hTC
  refine ⟨C,hCY,hp,hTC',hk,hcc,hmap.symm ▸ hcomm,hmap.symm ▸ hbound,?_⟩
  intro hP
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hSC : (S : Subgroup J) ≤ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact fun _ hx => hTC hx
  have hSN : (S : Subgroup J).map q ≤ normalizer (C.map q : Set (HStar J)) :=
    (map_mono hSC).trans (le_normalizer_map q)
  have hall : (⊤ : Subgroup (HStar J)) ≤ normalizer (C.map q : Set (HStar J)) := by
    have ht := pResidual_sup_sylow_eq_top (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
    rw [hr] at ht
    rw [←ht]
    exact sup_le hP hSN
  have hQC : q.ker ≤ normalizer (C : Set J) := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSC
  have hJC : (⊤ : Subgroup J) ≤ normalizer (C : Set J) :=
    (map_le_normalizer_map_iff_of_pPerfect q C ⊤ hp hkq hQC).mp
      (le_top.trans hall)
  apply hout
  have hh := (map_mono (f := J.subtype) hJC).trans (le_normalizer_map J.subtype)
  simpa only [←MonoidHom.range_eq_map,range_subtype,hmap] using hh


/-- The normal nine branch cannot have abelian three-core: that core would
fix the cubic action-kernel line, contrary to its proved movement. -/
theorem local_solvable_nine_threeCore_not_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ¬ IsMulCommutative (pCore 3 (HStar J)) := by
  intro habP
  let := habP
  obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let q := QuotientGroup.mk' (pCore 2 J)
  let eY := (coreQuotientEquivImage 2 Y).symm.trans e
  have h3 : IsPGroup 3 (Y.map q) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr eY.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let : (Y.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hYP : Y.map q ≤ pCore 3 (HStar J) := le_sSup ⟨inferInstance,h3⟩
  exact hout ((le_centralizer (pCore 3 (HStar J))).trans
    ((centralizer_le ((map_mono hCY).trans hYP)).trans
      (Subgroup.centralizer_le_normalizer _)))

/-- The original minimal witness supplies a moving cubic kernel line in the
nine branch; the Heisenberg center marking is preserved. -/
theorem local_minimal_solvable_threeCore_kernel_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          Y.map I.subtype ≤ normalizer (L : Set G) ∧
          ¬ IsMulCommutative (pCore 3 (HStar I)) ∧
          ∃ C : Subgroup I, C ≤ Y ∧ IsPPerfect 2 C ∧
            (T : Subgroup G) ≤ normalizer (C.map I.subtype : Set G) ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp C.subtype).ker = pCore 2 C ∧
            Nat.card (C.map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
            ⁅L,C.map I.subtype⁆ ≤ L.pCoreIn 2 ∧
            normalizer (C.map I.subtype : Set G) ≤ normalizer (L : Set G) ∧
            ¬ pCore 3 (HStar I) ≤ normalizer
              (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,_,he⟩ :=
    local_minimal_solvable_threeCore_nine_containment h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,?_⟩
  rcases he with ⟨he,hr,hM⟩ | he
  · exact Or.inl ⟨he,hr,hM,local_solvable_nine_threeCore_not_abelian
      h hab structural previous faithful I hI hIs Y hYp hAY he.some hr,
      local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful I hI hIs Y hYp hAY he.some hr⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
