module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointQuotient
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.GeneralizedFitting.ComponentImageNormalizer

/-!
# The original outside-core component and central local covers

The complementary point moves an ordinary component of the point join J.
Its image survives O₃′(J), since that kernel is solvable. The genuine
F.6.10 component reduction orients the image; F.6.13 forces both local
residuals into it because both quotient vertices have characteristic two.
Thus the quotient's two-residual is its quasisimple generalized Fitting
subgroup. Component normality reflects through the quotient, and the
prime-to-three residual lifts across O₃′(J), identifying the original
ordinary component with O²(J).

Consequently both actual local residuals centralize O₂(J). Their existing
surjections onto A₄ therefore have central two-group kernels, with the
literal double subgroup restrictions retained. SourceAssembly/PointComponent
applies these results throughout the original universal terminal argument.

The final A₃-block lift/exclusion, FF core branch, nonsolvable generation
and single-factor endgame remain with qt-d-1367-assembly. Earlier Context,
13.3.2, C.1.32 and 5.2.3 keep their producers and qt-d-1361-source retains
final discharge. No full 13.2.7 or 13.6.7 is asserted here.

Source: Aschbacher--Smith 13.2.12, printed p.883; F.6.10, F.6.13 and
F.6.17, printed pp.306--309.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module

private theorem surviving_component_residual
    {J : Type*} [Group J] [Finite J] {A B : Subgroup J}
    (hSQ : IsSQTK KnownSimple.IsKnownSimple J)
    (hg : ChapterF.IsGoldschmidtTriple A B)
    (hqg : ChapterF.IsGoldschmidtTriple
      (A.map (QuotientGroup.mk' (pPrimeCore 3 J)))
      (B.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (hA : generalizedFitting (A.map (QuotientGroup.mk' (pPrimeCore 3 J))) =
      pCore 2 (A.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (hB : generalizedFitting (B.map (QuotientGroup.mk' (pPrimeCore 3 J))) =
      pCore 2 (B.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (K : Subgroup J) (hK : IsComponent J K) :
    K = pResidual 2 J ∧
      K.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
        pResidual 2 (J ⧸ pPrimeCore 3 J) ∧
      pResidual 2 (J ⧸ pPrimeCore 3 J) = generalizedFitting (J ⧸ pPrimeCore 3 J) := by
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let D := J ⧸ pPrimeCore 3 J
  let Kq := K.map q
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let : Group.IsSolvable (pPrimeCore 3 J) := hg.primeToThreeCore_solvable
  have hne : Kq ≠ ⊥ := by
    intro he
    have hle : K ≤ pPrimeCore 3 J := by
      simpa only [Subgroup.map_eq_bot_iff, Kq, q, QuotientGroup.ker_mk'] using he
    exact Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))
  have hKq : IsComponent D Kq :=
    (hK.map_surjective q (QuotientGroup.mk'_surjective _)).resolve_left hne
  obtain ⟨hn,horient⟩ := ChapterF.SourceAssembly.source_lemma_F_6_10_sqtk_quotient
    ChapterA.Section02.theoremA_knownSimple hSQ (MulEquiv.refl _) hqg hKq
  let : Kq.Normal := hn
  have hcore : pCore 2 D = ⊥ := hg.primeToThreeCore_quotient_twoCore_eq_bot
  have hboth : (pResidual 2 (A.map q)).map (A.map q).subtype ≤ Kq ∧
      (pResidual 2 (B.map q)).map (B.map q).subtype ≤ Kq := by
    rcases horient with ⟨ha,_⟩ | ⟨hb,_⟩
    · refine ⟨ha,?_⟩
      by_contra hb
      exact ChapterF.SourceAssembly.left_not_characteristic_two_of_residual_cubic hqg
        (ChapterF.SourceAssembly.left_residual_card_three_of_normal_subgroup hqg hcore Kq ha hb) hA
    · refine ⟨?_,hb⟩
      by_contra ha
      exact ChapterF.SourceAssembly.left_not_characteristic_two_of_residual_cubic hqg.symm
        (ChapterF.SourceAssembly.left_residual_card_three_of_normal_subgroup hqg.symm hcore Kq hb ha) hB
  let : IsQuasisimple Kq := hKq.2
  obtain ⟨hR,hF,_⟩ := ChapterF.SourceAssembly.quasisimple_residual_of_both_local_containments
    hqg (pPrimeCore_quotient_pPrimeCore_eq_bot 3) Kq hboth.1 hboth.2
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique (by
    intro x _
    exact hK.mem_normalizer_of_mem_normalizer_map q hne
      (by rw [normalizer_eq_top]; exact mem_top _)))
  have hp : IsPPerfect 2 K := by
    intro N hN hquot
    let : N.Normal := hN
    by_contra hNtop
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
    let : Group.IsPerfect (K ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hKR : K ≤ primeToResidual 3 J :=
    (le_pResidual_of_isPPerfect K hp).trans_eq hg.twoResidual_eq_primeToThreeResidual
  have he := eq_primeToResidual_of_coprime_quotient_image 3 (pPrimeCore 3 J) K
    pPrimeCore_coprime_card hKR (hR.symm.trans hqg.twoResidual_eq_primeToThreeResidual)
  exact ⟨he.trans hg.twoResidual_eq_primeToThreeResidual.symm,hR.symm,hR.trans hF.symm⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

/-- In the outside-core branch the actual point join has an ordinary
quasisimple two-residual. Its image is the quotient's generalized Fitting subgroup. -/
theorem point_join_residual_component_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hJv : P₁ ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) ≤
      Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q →
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2 →
    IsComponent J (pResidual 2 J) ∧
      (pResidual 2 J).map q = pResidual 2 (J ⧸ pPrimeCore 3 J) ∧
      pResidual 2 (J ⧸ pPrimeCore 3 J) = generalizedFitting (J ⧸ pPrimeCore 3 J) ∧
      pResidual 2 J ≤ centralizer (pCore 2 J : Set J) := by
  intro P₂ J A B q hi hSQ hg hqg hqi hout
  obtain ⟨_,K,hK,_,_⟩ := point_overgroup_component_of_complement_not_mem_core d hH hB hZ hs hz
    (hBP.trans le_sup_left) (le_sup_left.trans le_sup_right) hJv hg hout
  obtain ⟨_,_,_,_,_,_,ha,hb,_,_⟩ := point_quotient_local_models_of_complement_not_mem_core
    d hH hB hZ hs hz horiginal hBP hJv hi hg hqg hqi hout
  obtain ⟨hR,himage,hF⟩ := surviving_component_residual hSQ hg hqg ha hb K hK
  have hr : IsComponent J (pResidual 2 J) := hR ▸ hK
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  exact ⟨hr,hR ▸ himage,hF,hr.le_centralizer_of_solvable_normal (pCore 2 J)⟩

/-- The previously constructed A₄ maps are central two-covers of both
original local residuals, with their literal ambient-core kernels. -/
theorem point_residual_central_covers_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hJv : P₁ ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) ≤
      Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q →
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2 →
    (∀ M ∈ ({A,B} : Set (Subgroup J)),
      ∃ f : pResidual 2 M →* alternatingGroup (Fin 4), Function.Surjective f ∧
        f.ker = ((pCore 2 J).subgroupOf M).subgroupOf (pResidual 2 M) ∧
        IsPGroup 2 f.ker ∧ f.ker ≤ center (pResidual 2 M)) := by
  intro P₂ J A B q hi hSQ hg hqg hqi hout M hM
  obtain ⟨_,_,_,hcent⟩ := point_join_residual_component_of_complement_not_mem_core
    d hH hB hZ hs hz horiginal hBP hJv hi hSQ hg hqg hqi hout
  obtain ⟨f,hf,hker⟩ := point_quotient_residual_A4_of_complement_not_mem_core
    d hH hB hZ hs hz horiginal hBP hJv hi hg hqg hqi hout M hM
  refine ⟨f,hf,hker,?_,?_⟩
  · rw [hker]
    exact pCore_isPGroup.comap_subtype.comap_subtype
  · intro x hx
    have hxQ : ((x : M) : J) ∈ pCore 2 J := by
      change x ∈ ((pCore 2 J).subgroupOf M).subgroupOf (pResidual 2 M)
      rwa [← hker]
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy : ((y : M) : J) ∈ pResidual 2 J :=
      map_pResidual_le 2 M.subtype (mem_map_of_mem M.subtype y.property)
    exact (mem_centralizer_iff.mp (hcent hy) x hxQ).symm

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
