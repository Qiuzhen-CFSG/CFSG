module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNinePoint
public import Theory.GroupTheory.PGroup.NormalNineInvariantActor
public import Theory.GroupTheory.PGroup.SupercriticalNineCyclic
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# T-invariant cyclic enlargement of the original normal nine-lift

In an original solvable J in H_z, the three-core acts nontrivially on the
normal elementary-nine image and fixes precisely the original point line.
Select a three-core actor whose cyclic subgroup is normalized by the actual
Sylow image. The canonical quotient-centralizing cubic residual is normalized
by J intersect N_G(L). An actor in that intersection would centralize both
cubic lines, so the selected actor escapes the literal normalizer image.

Lift its cyclic subgroup to a two-perfect T-invariant subgroup, retaining the
full two-core kernel. If the actor has order three, the proved cubic-containment
argument gives a contradiction. For higher three-power order, supercriticality
puts the fixed point line in its cyclic subgroup. Two-perfectness then lifts
point containment through the exact kernel. Adjoining T gives an escaping
local with cyclic three-residual, contrary to the original Sylow bound.

This excludes the elementary-nine supercritical branch in the original minimal
solvable witness. The final application constructs its remaining Heisenberg
branch directly from the original solvability assumption, preserving relative
point normality, its center marking and the literal quotient kernel. Terminal
Heisenberg exclusion and the component reductions through 14.7.52 remain.

Source: Aschbacher–Smith, 14.5.20, printed pp.1018–1019, and
14.7.27–29, printed pp.1054–1055, refs/quasithin.pdf.
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

/-- Select a three-core actor escaping the actual seed-normalizer image,
centralizing the point line and generating a T-invariant cyclic subgroup. -/
theorem local_solvable_nine_invariant_actor
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
    let q := QuotientGroup.mk' (pCore 2 J)
    let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
    let A := ((F.Li L 1).subgroupOf J).map q
    ∃ y : HStar J, y ∈ pCore 3 (HStar J) ∧
      y ∉ centralizer (Y.map q : Set (HStar J)) ∧ y ∉ Y.map q ∧
      y ∈ centralizer (A : Set (HStar J)) ∧
      (S : Subgroup J).map q ≤ normalizer (zpowers y : Set (HStar J)) ∧
      y ∉ ((normalizer (L : Set G)).subgroupOf J).map q := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let A := ((F.Li L 1).subgroupOf J).map q
  let M := normalizer (L : Set G)
  obtain ⟨hAn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hAn
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let eN := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsElementaryAbelian 3 N := IsElementaryAbelian.of_injective eN.toMonoidHom eN.injective
  have h9 : Nat.card N = 9 := by
    rw [Nat.card_congr eN.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hmove : ¬ P ≤ centralizer (N : Set (HStar J)) := by
    intro hc
    obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
    exact hout (hc.trans ((centralizer_le (map_mono hCY)).trans
      (Subgroup.centralizer_le_normalizer _)))
  obtain ⟨y,hyP,hyN,hSy⟩ := normal_nine_normalized_actor P N ((S : Subgroup J).map q)
    pCore_isPGroup (S.isPGroup'.map q) h9 hmove
  have hyout : y ∉ N := fun hy => hyN (le_centralizer N hy)
  have hAP : A ≤ centralizer (P : Set (HStar J)) := by
    rw [show A = N ⊓ centralizer (P : Set (HStar J)) from hfixed]
    exact inf_le_right
  have hyA : y ∈ centralizer (A : Set (HStar J)) := le_centralizer_iff.mp hAP hyP
  refine ⟨y,hyP,hyN,hyout,hyA,hSy,?_⟩
  let D := pCoreActionKernelIn 2 L (Y.map J.subtype)
  let C₀ := (pResidual 2 D).map D.subtype
  obtain ⟨hCB,hCp,hTC,hc,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_lift h hab structural previous faithful J hJ hs Y hYp hAY e
  have hCJ : C₀ ≤ J := hCB.trans (map_subtype_le Y)
  let C := C₀.subgroupOf J
  have hCm : C.map J.subtype = C₀ := map_subgroupOf_eq_of_le hCJ
  have hCY : C ≤ Y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hCm]
    exact hCB
  let eC := subgroupOfEquivOfLe hCJ
  have hpC : IsPPerfect 2 C := hCp.of_surjective eC.symm.toMonoidHom eC.symm.surjective
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).toEquiv).trans hc
  let f := q.comp C.subtype
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkf : IsPGroup 2 f.ker := hkq.comap_of_injective _ C.subtype_injective
  have h3N : IsPGroup 3 N := IsPGroup.of_card (n := 2) (by simpa using h9)
  have hfr : f.range = C.map q := by rw [MonoidHom.range_comp,range_subtype]
  have h3f : IsPGroup 3 f.range := hfr.symm ▸ h3N.to_le (map_mono hCY)
  have h2f : pCore 2 f.range = ⊥ :=
    bot_unique ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (h3f.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hkf' : f.ker = pCore 2 C := f.ker_eq_pCore_of_range_core_eq_bot 2 hkf h2f
  have h3C : Nat.card (C.map q) = 3 := by
    rw [←hfr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hkf']
    exact hcC
  have hSC : (S : Subgroup J) ≤ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact fun _ hx => hTC hx
  have hkC : q.ker ≤ normalizer (C : Set J) := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSC
  have hne : A ≠ C.map q := by
    intro he
    have hnorm : (⊤ : Subgroup J) ≤ normalizer (C : Set J) :=
      (map_le_normalizer_map_iff_of_pPerfect q C ⊤ hpC hkq hkC).mp (by
        rw [←he]
        exact le_normalizer_of_normal)
    apply hout
    have hh := (map_mono (f := J.subtype) hnorm).trans (le_normalizer_map J.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype,hCm] using hh
  have h3A : Nat.card A = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hdis : Disjoint A (C.map q) := by
    have hd : Nat.card (A ⊓ C.map q : Subgroup (HStar J)) ∣ 3 :=
      h3A ▸ card_dvd_of_le (inf_le_left : A ⊓ C.map q ≤ A)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have hAe : A ⊓ C.map q = A := eq_of_le_of_card_ge inf_le_left (by rw [h3,h3A])
      have hCe : A ⊓ C.map q = C.map q := eq_of_le_of_card_ge inf_le_right (by rw [h3,h3C])
      exact (hne (hAe.symm.trans hCe)).elim
  have hgen : A ⊔ C.map q = N := by
    apply eq_of_le_of_card_ge (sup_le (map_mono hAY) (map_mono hCY))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (C.map q)
      le_normalizer_of_normal hdis,h3A,h3C,h9]
  have hJB : J ≤ normalizer (Y.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hMD : M ≤ normalizer
      (((pCoreNormalizerAction 2 L).ker).map M.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCoreNormalizerAction 2 L).ker.le_normalizer_map M.subtype
  have hJMC : J ⊓ M ≤ normalizer (C₀ : Set G) :=
    ((le_inf (inf_le_left.trans hJB) (inf_le_right.trans hMD)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  intro hym
  obtain ⟨x,hx,hxy⟩ := hym
  have hxC : x ∈ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact hJMC ⟨x.property,hx⟩
  have hyC : y ∈ normalizer (C.map q : Set (HStar J)) :=
    hxy ▸ le_normalizer_map q (mem_map_of_mem q hxC)
  let : Normalizes (zpowers y) (C.map q) := ⟨zpowers_le.mpr hyC⟩
  have hyCp : IsPGroup 3 (zpowers y) :=
    (pCore_isPGroup (p := 3) (G := HStar J)).to_le (zpowers_le.mpr hyP)
  have htriv := actsTrivially_of_isPGroup_on_cyclic_prime_order
    (A := zpowers y) (G := C.map q) Nat.prime_three hyCp
    (isCyclic_of_prime_card h3C) h3C
  have hyCC : y ∈ centralizer (C.map q : Set (HStar J)) := by
    intro c hc
    have hh := congrArg Subtype.val (htriv ⟨y,mem_zpowers y⟩ ⟨c,hc⟩)
    change y * c * y⁻¹ = c at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply hyN
  rw [←hgen]
  exact le_centralizer_iff.mp
    (sup_le (le_centralizer_iff.mpr (zpowers_le.mpr hyA))
      (le_centralizer_iff.mpr (zpowers_le.mpr hyCC))) (mem_zpowers y)

/-- A two-perfect T-invariant cyclic three-lift containing the original
point residual lies in the seed normalizer. -/
theorem local_cyclic_three_lift_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (W : Subgroup J) (hWp : IsPPerfect 2 W)
    (hTW : (T : Subgroup G) ≤ normalizer (W.map J.subtype : Set G))
    (hAW : (F.Li L 1).subgroupOf J ≤ W)
    (hcyc : IsCyclic (W ⧸ pCore 2 W))
    (h3 : IsPGroup 3 (W ⧸ pCore 2 W)) :
    W.map J.subtype ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let E := W.map J.subtype
  let D := E ⊔ (T : Subgroup G)
  have hEJ : E ≤ J := map_subtype_le W
  have hDJ : D ≤ J := sup_le hEJ (F.sylow_le_of_mem_Hz hJ)
  have hED : E ≤ D := le_sup_left
  have hTD : (T : Subgroup G) ≤ D := le_sup_right
  have hAE : F.Li L 1 ≤ E := by
    have hh := map_mono (f := J.subtype) hAW
    rwa [map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ)] at hh
  have hAD : F.Li L 1 ≤ D := hAE.trans hED
  have hDH : D ≤ F.H := hDJ.trans hJ.2.1
  have hpoint : F.Vi 1 ≤ D.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using F.card 1 (by decide)))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)) hDH
  have hcore : D.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hh := le_bot_iff.mp (hz ▸ hpoint)
    have hc := F.card 1 (by decide)
    rw [hh,card_bot] at hc
    norm_num at hc
  have hD : D ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hAD ha) (fun ht => hTD ht)⟩,
      hDH,fun hh => hout (hED.trans hh)⟩
  have hEp : IsPPerfect 2 E := hWp.of_surjective (J.subtype.subgroupMap W)
    (J.subtype.subgroupMap_surjective W)
  let Z := E.subgroupOf D
  let : Z.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.le_normalizer hTW)
  have hres : pResidual 2 D = Z := by
    apply map_injective D.subtype_injective
    rw [embedded_pResidual_join_pGroup E (T : Subgroup G) hEp T.isPGroup' hTW,
      map_subgroupOf_eq_of_le hED]
  let eZ : Z ≃* W := (subgroupOfEquivOfLe hED).trans
    (equivMapOfInjective W J.subtype J.subtype_injective).symm
  let eQ := QuotientGroup.congr _ _ eZ (pCore_map_iso 2 eZ)
  let qD := QuotientGroup.mk' (pCore 2 D)
  let eim : Z.map qD ≃* (W ⧸ pCore 2 W) :=
    (coreQuotientEquivImage 2 Z).symm.trans eQ
  let := hcyc
  have hcycim : IsCyclic (Z.map qD) := isCyclic_of_surjective eim.symm eim.symm.surjective
  have h3im : IsPGroup 3 (Z.map qD) := h3.of_equiv eim.symm
  have hrim : pResidual 2 (HStar D) = Z.map qD := by
    rw [←map_pResidual_of_surjective 2 qD (QuotientGroup.mk'_surjective _),hres]
  exact no_cyclic_three_local_star_residual h hab structural D hD
    ⟨hrim ▸ hcycim,hrim ▸ h3im⟩

/-- Exclude the marked elementary-nine supercritical branch in an original
solvable local, with the full star-map kernel retained. -/
theorem local_solvable_supercritical_nine_exclusion
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) =
      X.map (pCore 3 (HStar J)).subtype)
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) : False := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let A₀ := (F.Li L 1).subgroupOf J
  let A := A₀.map q
  obtain ⟨hAn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hAn
  obtain ⟨y,hyP,hyN,hyout,hyA,hSy,hyM⟩ := local_solvable_nine_invariant_actor
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcy : IsPGroup 3 (zpowers y) :=
    (pCore_isPGroup (p := 3) (G := HStar J)).to_le (zpowers_le.mpr hyP)
  obtain ⟨W,_,hWp,hWm,hWA,hWK,hWk,⟨eW⟩⟩ := exists_three_lift_within_normal
    q hkq ⊤ (zpowers y) ((S : Subgroup J).map q)
    (by rw [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]; exact le_top)
    hSy hcy
  have hSW : (S : Subgroup J) ≤ normalizer (W : Set J) :=
    (le_comap_map q _).trans hWA
  have hTW : (T : Subgroup G) ≤ normalizer (W.map J.subtype : Set G) := by
    intro t ht
    let tJ : J := ⟨t,F.sylow_le_of_mem_Hz hJ ht⟩
    exact le_normalizer_map J.subtype (mem_map_of_mem J.subtype
      (hSW (show tJ ∈ (S : Subgroup J) from ht)))
  have hWout : ¬ W.map J.subtype ≤ normalizer (L : Set G) := by
    intro hh
    have hWM : W ≤ (normalizer (L : Set G)).subgroupOf J :=
      fun w hw => hh (mem_map_of_mem J.subtype hw)
    exact hyM ((map_mono hWM) (hWm.symm ▸ mem_zpowers y))
  have hWpG : IsPPerfect 2 (W.map J.subtype) := hWp.of_surjective
    (J.subtype.subgroupMap W) (J.subtype.subgroupMap_surjective W)
  by_cases ho : orderOf y = 3
  · apply hWout
    apply local_solvable_cubic_containment h hab structural previous faithful J hJ hs
      (W.map J.subtype) (map_subtype_le W)
      ((map_subtype_le W).trans (F.normalizes_Li_one_of_relative_normal hJ)) hWpG hTW
    let eG := (equivMapOfInjective W J.subtype J.subtype_injective).symm
    let eGQ := QuotientGroup.congr _ _ eG (pCore_map_iso 2 eG)
    rw [Nat.card_congr eGQ.toEquiv,Nat.card_congr eW.toEquiv,Nat.card_zpowers,ho]
  · let eN := (coreQuotientEquivImage 2 Y).symm.trans e
    let eX := ((equivMapOfInjective X P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hm.symm)).trans eN
    let : IsElementaryAbelian 3 X :=
      IsElementaryAbelian.of_injective eX.toMonoidHom eX.injective
    have h9X : Nat.card X = 9 := by
      rw [Nat.card_congr eX.toEquiv,Nat.card_prod]
      norm_num [Nat.card_zmod]
    let yP : P := ⟨y,hyP⟩
    have hyn : yP ∉ centralizer (X : Set P) := by
      intro hh
      apply hyN
      intro x hx
      rw [hm] at hx
      obtain ⟨a,ha,rfl⟩ := hx
      exact congrArg Subtype.val (hh a ha)
    have hoP : orderOf yP ≠ 3 := fun hh => ho ((Subgroup.orderOf_coe yP).trans hh)
    have hAX := supercritical_nine_fixed_line_le_zpowers pCore_isPGroup X hX h9X yP hyn hoP
    have hAZ : A ≤ zpowers y := by
      intro a ha
      have ha' : a ∈ N ⊓ centralizer (P : Set (HStar J)) := hfixed ▸ ha
      have haN : a ∈ X.map P.subtype := hm ▸ ha'.1
      obtain ⟨x,hx,hxa⟩ := haN
      have hxC : x ∈ centralizer (⊤ : Set P) := by
        intro b hb
        apply Subtype.ext
        change (b : HStar J) * P.subtype x = P.subtype x * (b : HStar J)
        rw [hxa]
        exact ha'.2 b b.property
      have hxZ := hAX ⟨hx,hxC⟩
      have hh : a ∈ (zpowers yP).map P.subtype := ⟨x,hxZ,hxa⟩
      rw [MonoidHom.map_zpowers] at hh
      change a ∈ zpowers y at hh
      exact hh
    have hAp : IsPPerfect 2 A₀ :=
      (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
        (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.toMonoidHom
        (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.surjective
    have hAW : A₀ ≤ W := isPPerfect_le_of_map_le_of_kernel_normalizes q A₀ W
      hAp hkq hWK (by rw [hWm]; exact hAZ)
    have hcyW : IsCyclic (W ⧸ pCore 2 W) :=
      isCyclic_of_surjective eW.symm eW.symm.surjective
    have h3W : IsPGroup 3 (W ⧸ pCore 2 W) := hcy.of_equiv eW.symm
    exact hWout (local_cyclic_three_lift_containment h hab structural J hJ W hWp hTW hAW hcyW h3W)

/-- A minimal solvable escaping local has only the marked Heisenberg
supercritical branch: the elementary-nine branch has been excluded. -/
theorem local_minimal_solvable_threeCore_heisenberg
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
      Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
        ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  rcases he with ⟨he,hr⟩ | ⟨he,hn,hcenter⟩
  · exact (local_solvable_supercritical_nine_exclusion h hab structural previous faithful
      I hI hIs X hX Y hYp hAY he.some hm hr).elim
  · exact ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he,hn,hcenter⟩

/-- The actual original point normalizer supplies a marked Heisenberg
witness under a solvability assumption, without an added local-model input. -/
theorem original_solvable_minimal_heisenberg
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ Y : Subgroup I, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
        (F.Li L 1).subgroupOf I ≤ Y ∧
        ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) := by
  obtain ⟨I,hIH,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he,hn,hcenter⟩ :=
    local_minimal_solvable_threeCore_heisenberg h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs
  exact ⟨I,hIH,hI,hIs,hmin,hn,Y,hYn,hYp,hYr,hAY,hk,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
