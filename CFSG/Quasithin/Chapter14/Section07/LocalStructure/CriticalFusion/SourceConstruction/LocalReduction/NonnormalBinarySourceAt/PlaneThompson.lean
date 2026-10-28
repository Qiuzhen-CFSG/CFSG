module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.ThompsonNormality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneNine
public import Theory.GroupTheory.TwoPerfectCubicKernel
public import Theory.GroupTheory.ElementaryThompsonSectionNormalizer
/-!
# Thompson movement in the original reciprocal-plane local

Retain the same Y, I₀, point span V_I and faithful nine-group from the
preceding construction. Suppose J(T) centralizes V_I. The nonzero L₁
image and its two-perfect cubic quotient force the kernel of the literal
L₁T action to be a two-group. Thus J(T) lies in R₁. Source 14.3.9 then
makes J(T) normal in LT, whose uniqueness puts N_G(J(T)) inside M.

The same J(T) centralizes the reciprocal plane and therefore normalizes
Y₀; it also normalizes the constructed R. Adjoining it to Y gives a
two-group plane centralizer inside T. Thompson heredity forces Y, and
hence Y₀, to normalize J(T), contradicting Y₀ not contained in M. This
argument avoids requiring the whole plane centralizer to lie in R₁.
Finally the actual subgroup embeddings transport movement to the
nonzero image of J(I₀) in I₀/C_{I₀}(V_I).

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. Small-factor selection and the cubic projection
contradiction remain subsequent steps. The guarded same-G,T successor,
remaining reductions through 14.7.52 and all four source Data duties
remain with the local assembly; this module adds no recognition premise.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
private theorem point_action_kernel_le_core {Q : Type*} [Group Q]
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (f : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) →* Q)
    (hne : ((F.Li L 1).subgroupOf (F.Li L 1 ⊔ (T : Subgroup G))).map f ≠ ⊥) :
    f.ker.map (F.Li L 1 ⊔ (T : Subgroup G)).subtype ≤ F.Ri L 1 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let A := (F.Li L 1).subgroupOf B
  let e : A ≃* F.Li L 1 := subgroupOfEquivOfLe le_sup_left
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (F.Li L 1).le_normalizer (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural)))
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hn : f.comp A.subtype ≠ 1 := by
    intro he
    apply hne
    apply bot_unique
    rintro x ⟨a,ha,rfl⟩
    exact DFunLike.congr_fun he ⟨a,ha⟩
  have hkA := (f.comp A.subtype).kernel_isTwoGroup_of_twoPerfect_cubic hp hc hn
  have hgen : A ⊔ (T : Subgroup G).subgroupOf B = ⊤ := by
    rw [show A = (F.Li L 1).subgroupOf B from rfl,
      ←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hk := f.kernel_isPGroup_of_normal_supplement A ((T : Subgroup G).subgroupOf B)
    T.isPGroup'.comap_subtype hgen hkA
  exact map_mono (show f.ker ≤ pCore 2 B from le_sSup ⟨inferInstance,hk⟩)

private theorem selected_thompson_moves
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (hE : IsElementaryAbelian 2 (F.Vi 1 ⊔ c.Zα : Subgroup G))
    (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4)
    (hR : c.Uα ≤ F.Ri L 1)
    (hSylow : Chapter1.IsSylowIn 2
      (F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)))
      ((F.H.pCoreIn 2 ⊔ c.Qα) ⊔
        (F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)))))
    (hcore :
      ((F.H.pCoreIn 2 ⊔ c.Qα) ⊔
        (F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)))) ⊓
      centralizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) =
      ((F.H.pCoreIn 2 ⊔ c.Qα) ⊔
        (F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)))).pCoreIn 2)
    (hRN : F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)) ≤
      normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G))
    (hescape : ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (L : Set G)) :
    let B := F.Li L 1 ⊔ (T : Subgroup G)
    let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα B
    let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
    let I₀ := B ⊔ Y
    let W := conjugateSpanBy (F.Vi 1) I₀
    letI : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
    ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ →
    F.Vi 1 ⊔ c.Zα ≤ W →
    ⁅W,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα B
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let Y := Y₀ ⊔ R
  let I₀ := B ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  change ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ →
    F.Vi 1 ⊔ c.Zα ≤ W → ⁅W,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥
  intro hne hPW hz
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJW : J ≤ centralizer (W : Set G) := le_centralizer_iff.mpr
    (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hJC : J ≤ centralizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) :=
    hJW.trans (centralizer_le hPW)
  let f := q.comp (inclusion (show B ≤ I₀ from le_sup_left))
  have hnf : ((F.Li L 1).subgroupOf B).map f ≠ ⊥ := by
    have he : ((F.Li L 1).subgroupOf B).map (inclusion (show B ≤ I₀ from le_sup_left)) =
        (F.Li L 1).subgroupOf I₀ := by
      apply map_injective I₀.subtype_injective
      rw [map_map]
      change ((F.Li L 1).subgroupOf B).map B.subtype = _
      rw [map_subgroupOf_eq_of_le le_sup_left,
        map_subgroupOf_eq_of_le (le_sup_left.trans le_sup_left)]
    simpa only [f,←map_map,he] using hne
  have hJR : J ≤ F.Ri L 1 := by
    apply le_trans _ (point_action_kernel_le_core h structural f hnf)
    intro x hx
    refine ⟨⟨x,mem_sup_right (hJT hx)⟩,?_,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    intro w hw
    apply Subtype.ext
    exact hJW hx w hw
  have hnJ := Chapter14.Section03.ThompsonSource.thompson_normal_at h F structural hJR
  have hLJ : L ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hnJ
  have hTne : (T : Subgroup G) ≠ ⊥ := fun hz =>
    h.chosen.ne_bot (eq_bot_iff.mpr (h.chosen.le_sylow.trans hz.le))
  have hJne := elementaryAbelianMaxJ_ne_bot_of_finite_pGroup (T : Subgroup G) T.isPGroup' hTne
  have hJM : normalizer (J : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from
          ⟨hM,hAM⟩)) (T.isPGroup'.to_le hJT) hJne hLJ
  obtain ⟨hY₀P,hNY⟩ := local_nonnormal_component_selected_plane_normalizers_at
    d h hab structural previous faithful earlier I K hI hKI hK hnormal c hs ha hE hfour
  obtain ⟨_,hRT,hBR⟩ := critical_plane_normal_span c hR
  have hJY : J ≤ normalizer (Y : Set G) :=
    (le_inf (hJC.trans ((Subgroup.centralizer_le_normalizer _).trans hNY))
      (hJT.trans (le_sup_right.trans hBR))).trans
        (normalizer_inf_normalizer_le_normalizer_sup Y₀ R)
  have hYP : Y ≤ normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) :=
    sup_le hY₀P hRN
  obtain ⟨S,hS⟩ := hSylow
  have hYJ := normalizes_maxJ_of_normalizing_centralized_section T Y (F.Vi 1 ⊔ c.Zα)
    hYP (by rw [hcore]; exact isPGroup_pCoreIn 2 Y) hJC hJY S (hS.le.trans hRT)
  exact hescape ((le_sup_left.trans hYJ).trans hJM)
private theorem thompson_top_image_ne_bot
    (D W : Subgroup G) (hTD : (T : Subgroup G) ≤ D) (hWD : W ≤ D)
    {Q : Type*} [Group Q] (q : D →* Q)
    (hk : q.ker = centralizer (W.subgroupOf D : Set D))
    (hm : ⁅W,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥) :
    (elementaryAbelianMaxJ (⊤ : Subgroup D)).map q ≠ ⊥ := by
  intro hz
  have hJker := (Subgroup.map_eq_bot_iff _).mp hz
  rw [hk] at hJker
  let S := T.subtype hTD
  have hmap : (elementaryAbelianMaxJ (S : Subgroup D)).map D.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD]
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro x hx w hw
  obtain ⟨a,ha,hax⟩ := show x ∈ (elementaryAbelianMaxJ (S : Subgroup D)).map D.subtype from
    hmap.symm ▸ hx
  subst x
  exact congrArg Subtype.val
    (hJker (elementaryAbelianMaxJ_sylow_le_top S ha) ⟨w,hWD hw⟩ hw)

/-- The original constructed local has nontrivial Thompson movement, retaining
its actual cubic pair and centralizer quotient. -/
theorem local_nonnormal_component_weakClosure_thompson_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
      let I₀ := J ⊔ Y
      let W₀ := ChapterE.indexedWeakClosure V R 0
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      R ≤ normalizer (P : Set G) ∧ Chapter1.IsSylowIn 2 R Y ∧
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
      Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
      V ≤ W₀ ∧ W₀ ≤ R ∧ I₀ ≤ normalizer (W₀ : Set G) ∧
      IsTwoLocal (normalizer (W₀ : Set G)) ∧ normalizer (W₀ : Set G) ≠ ⊤ ∧
      I₀ = J ⊔ c.Qα ∧ HasCharacteristicTwo I₀ ∧
      IsSQTK KnownSimple.IsKnownSimple I₀ ∧
      IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) ∧
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ ∧
      ⁅conjugateSpanBy (F.Vi 1) I₀,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ ∧
      letI : ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀).Normal :=
        normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk'
        (centralizer ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀))
      (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ≠ ⊥ ∧
      ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal ∧
        ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (L : Set G) ∧
        Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) ∧
        let RY := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
        RY ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
          ∃ l : F.H, (l:G) ∈ RY ∧ orderOf (l:G)=3 ∧
            zpowers (l:G) ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
            ∃ y ∈ F.H.pCoreIn 2 ⊔ c.Qα, orderOf y = 3 ∧ Commute (l : G) y ∧
              IsElementaryAbelian 3 (zpowers y ⊔ zpowers (l : G) : Subgroup G) ∧
              Nat.card (zpowers y ⊔ zpowers (l : G) : Subgroup G) = 9 ∧
              Nat.card (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) = 9 ∧
              J ⊔ (zpowers y ⊔ zpowers (l : G)) = I₀ ∧
              ¬ ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                normalizer (((F.Li L 1).subgroupOf I₀).map q : Set _) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot⟩ :=
    local_nonnormal_component_weakClosure_nine_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  have hmove := selected_thompson_moves d h hab structural previous faithful earlier
    I K hI hKI hK hnormal c hs ha hE hfour hR hSylow hcore hRN hescape hne hPVI
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα B
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := B ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  have hTI : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  have hJplus := thompson_top_image_ne_bot I₀ W hTI
    (hVIW.trans (hWR.trans (hRT.trans hTI))) q (QuotientGroup.ker_mk' _) hmove
  exact ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
