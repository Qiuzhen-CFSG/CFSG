module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneFactors
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import Theory.GroupTheory.ReducedNormal.SubnormalImage

/-!
# The nonsolvable factor of the original Thompson action

SQTK component generation selects an actual C-component of J(I) with
nontrivial image on the reduced normal elementary subgroup U. This
selection uses the original Thompson group and its literal action map;
no solvability of the action kernel is needed. The reduced commutator
lies in the component's intrinsic signalizer module, proving membership
in the faithful local family before applying the earlier 14.3.4 input.

That input identifies the component modulo its two-core with A₅ or L₃(2)
and makes the ambient Sylow subgroup normalize it. The component orbit
bound makes the two-residual normalize it as well, so the component is
normal in I. Reducedness kills its two-core action, and simplicity of
the marked quotient proves that this is the exact kernel on U.

Combining this with the solvable factor selection gives an actual S₃,
A₅ or L₃(2) factor for the same constructed Y, I₀ and reciprocal plane.
The original point residual and faithful nine-group normalize this factor.
The cubic projection contradiction, guarded same-G,T specialization,
and remaining reductions through 14.7.52 are still separate obligations.
The existing earlier faithful-classification input is preserved.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1058–1059,
using 1.2.10 and 14.3.4(1–2), refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB.InternalThompsonAction Chapter7.NormalizedSource.DoubledBinaryThompson
open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {D : Type u} [Group D] [Finite D]

private theorem sqtk_core_quotient (hD : IsSQTK KnownSimple.IsKnownSimple D) :
    IsSQTK KnownSimple.IsKnownSimple (D ⧸ pCore 2 D) := by
  refine ⟨?_,hD.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hD.stronglyQuasithin p hp ho)

private theorem sqtk_component_generation (hD : IsSQTK KnownSimple.IsKnownSimple D) :
    cComponentLayer D = solvableResidual D :=
  Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun _X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
    (sqtk_core_quotient hD)

private theorem exists_component_moving_image
    {Q : Type*} [Group Q] [Finite Q]
    (hD : IsSQTK KnownSimple.IsKnownSimple D) (f : D →* Q)
    (hf : Function.Surjective f) (hs : ¬ Group.IsSolvable Q) :
    ∃ C : Subgroup D, C.IsCComponent ∧ C.map f ≠ ⊥ := by
  by_contra! hz
  have hc : (cComponentLayer D).map f = ⊥ := by
    apply le_bot_iff.mp
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro C hC
    exact map_le_iff_le_comap.mp (hz C hC).le
  rw [sqtk_component_generation hD,map_solvableResidual_eq f hf] at hc
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := Q)
  exact hs ⟨n,hn.trans hc⟩

/-- A nonsolvable Thompson image supplies an original moving C-component. -/
theorem nonsolvable_reduced_thompson_component
    (U : Subgroup D) [U.Normal] [IsElementaryAbelian 2 U]
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (hs : ¬ Group.IsSolvable (thompsonImage U)) :
    ∃ C : Subgroup D, C ≤ elementaryAbelianMaxJ (⊤ : Subgroup D) ∧
      (C.subgroupOf (elementaryAbelianMaxJ (⊤ : Subgroup D))).IsCComponent ∧
      C.IsCComponent ∧ C.map (actionMk U) ≠ ⊥ := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup D)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  let q := actionMk U
  obtain ⟨B,hB,hne⟩ := exists_component_moving_image (hD.subgroup J)
    (q.subgroupMap J) (q.subgroupMap_surjective J) hs
  let C := B.map J.subtype
  have hm : C.subgroupOf J = B := comap_map_eq_self_of_injective J.subtype_injective B
  refine ⟨C,map_subtype_le B,hm.symm ▸ hB,
    IsCComponent.map_subtype (inferInstance : J.Normal).isSubnormal hB,?_⟩
  intro hz
  apply hne
  apply (map_eq_bot_iff_of_injective _ (J.map q).subtype_injective).mp
  rw [map_map]
  have hf : (J.map q).subtype.comp (q.subgroupMap J) = q.comp J.subtype := by ext; rfl
  rw [hf,←map_map]
  exact hz

private theorem intrinsic_nontrivial_of_reduced_moved
    (U C : Subgroup D) (hr : IsPReduced 2 U) (hC : C.IsCComponent)
    (hm : ⁅U,C⁆ ≠ ⊥) : intrinsicSignalizerModule C ≠ ⊥ := by
  let := hC.perfect
  have hp : IsPPerfect 2 C := by
    intro N hn htwo
    let := hn
    let := htwo.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hl := (commutator_mono hr.le_reducedPSubgroup (le_refl C)).trans
    (reduced_commutator_le_intrinsicModule C hC.subnormal hp)
  exact fun hz => hm (bot_unique (hz ▸ hl))

private theorem reduced_simple_ker (U C : Subgroup D) [U.Normal]
    (hr : IsPReduced 2 U) (hC : C.IsSubnormal)
    [IsSimpleGroup (C ⧸ pCore 2 C)]
    (hne : C.map (actionMk U) ≠ ⊥) :
    ((actionMk U).subgroupMap C).ker = pCore 2 C := by
  let q := actionMk U
  let f := q.subgroupMap C
  have hc : pCore 2 C ≤ f.ker := by
    have hl := hr.core_centralizes_of_subnormal_image C
      (hC.map (QuotientGroup.mk'_surjective _))
    intro c hc
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (c:D)).mpr (hl (mem_map_of_mem C.subtype hc))
  let f₀ := QuotientGroup.lift (pCore 2 C) f hc
  have hk : f₀.ker = ⊥ := by
    rcases (inferInstance : f₀.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      apply hne
      apply (map_eq_bot_iff C).mpr
      intro c hc
      have he : f₀ (QuotientGroup.mk' (pCore 2 C) (⟨c,hc⟩ : C)) = 1 :=
        ht.ge (mem_top _)
      exact congrArg Subtype.val he
  apply le_antisymm _ hc
  intro c hc
  have he : QuotientGroup.mk' (pCore 2 C) c ∈ f₀.ker := hc
  exact (QuotientGroup.eq_one_iff c).mp (mem_bot.mp (hk.le he))

variable {G : Type u} [Group G] [Finite G]

/-- Select and classify a moving component of the literal Thompson image.
Its original lift is normal in I, and the image has exactly its two-core kernel. -/
theorem nonsolvable_reduced_thompson_normal_factor
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hTI : (T : Subgroup G) ≤ I)
    (hI : I ∈ Chapter1.H G) (hD : IsSQTK KnownSimple.IsKnownSimple I)
    (U : Subgroup I) [U.Normal] [IsElementaryAbelian 2 U]
    (hr : IsPReduced 2 U) (hs : ¬ Group.IsSolvable (thompsonImage U)) :
    ∃ C : Subgroup I, C ≤ elementaryAbelianMaxJ (⊤ : Subgroup I) ∧
      (C.subgroupOf (elementaryAbelianMaxJ (⊤ : Subgroup I))).IsCComponent ∧
      C.IsCComponent ∧ C.Normal ∧
      C.map I.subtype ∈ Chapter1.LStar G T ∧
      IsFaithfulSignalizerType (C.map I.subtype) ∧
      ((actionMk U).subgroupMap C).ker = pCore 2 C ∧
      (Nonempty (C.map (actionMk U) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (C.map (actionMk U) ≃* Matrix.PSL3Two.PSL)) := by
  obtain ⟨C,hCJ,hCJcomp,hC,hne⟩ := nonsolvable_reduced_thompson_component U hD hs
  let B := C.map I.subtype
  have hBI : B ≤ I := map_subtype_le C
  have hBC : B.subgroupOf I = C := comap_map_eq_self_of_injective I.subtype_injective C
  have hlocal : B ∈ Chapter1.L G T :=
    Chapter1.mem_L_of_cComponent hI
      ⟨T.subtype hTI,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI]⟩
      hBI (hBC.symm ▸ hC)
  have hm : ⁅U,C⁆ ≠ ⊥ := by
    intro hz
    apply hne
    apply (map_eq_bot_iff C).mpr
    rw [actionMk,QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hfaith : IsFaithfulSignalizerType B := by
    refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T hE hlocal,?_⟩
    rw [show B = C.map I.subtype from rfl,
      intrinsicSignalizerModule_map_of_injective I.subtype I.subtype_injective]
    exact fun hz => intrinsic_nontrivial_of_reduced_moved U C hr hC hm
      ((map_eq_bot_iff_of_injective _ I.subtype_injective).mp hz)
  obtain ⟨hmodels,hBT,hmax⟩ := faithful B hlocal hfaith
  have hTN : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).mp hBT)
  have hn : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top (T.subtype hTI)]
    refine sup_le (Chapter1.Section02.twoPerfect_normalizes_cComponent_source
      (sqtk_core_quotient hD) hC (isPPerfect_pResidual 2)) ?_
    rw [Sylow.coe_subtype,←hBC,←subgroupOf_normalizer_eq hBI]
    exact comap_mono hTN
  let e : C ≃* B := C.equivMapOfInjective I.subtype I.subtype_injective
  let eq : (C ⧸ pCore 2 C) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hmodelsC : Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) :=
    hmodels.imp (fun ⟨f⟩ => ⟨eq.trans f⟩) (fun ⟨f⟩ => ⟨eq.trans f⟩)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := by
    rcases hmodelsC with hf | hf
    · obtain ⟨f⟩ := hf
      exact f.isSimpleGroup
    · obtain ⟨f⟩ := hf
      let : IsSimpleGroup Matrix.PSL3Two.PSL :=
        Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact f.isSimpleGroup
  have hk := reduced_simple_ker U C hr hC.subnormal hne
  let ei : (C ⧸ pCore 2 C) ≃* C.map (actionMk U) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((actionMk U).subgroupMap_surjective C))
  exact ⟨C,hCJ,hCJcomp,hC,hn,hmax,hfaith,hk,
    hmodelsC.imp (fun ⟨f⟩ => ⟨ei.symm.trans f⟩) (fun ⟨f⟩ => ⟨ei.symm.trans f⟩)⟩

/-- The nontrivial literal Thompson action has an actual small factor
preserved by all two-perfect actors, in either solvability branch. -/
theorem reduced_thompson_small_factor
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hTI : (T : Subgroup G) ≤ I)
    (hI : I ∈ Chapter1.H G) (hD : IsSQTK KnownSimple.IsKnownSimple I)
    (U : Subgroup I) [U.Normal] [IsElementaryAbelian 2 U]
    (hr : IsPReduced 2 U) (hne : thompsonImage U ≠ ⊥) :
    ∃ A : Subgroup (ActionQuotient U), A ≤ thompsonImage U ∧
      (A.subgroupOf (thompsonImage U)).Normal ∧ A.IsSubnormal ∧
      (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
        A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (A ≃* Matrix.PSL3Two.PSL))) ∧
      ∀ B : Subgroup (ActionQuotient U), IsPPerfect 2 B →
        B ≤ normalizer (A : Set (ActionQuotient U)) := by
  classical
  by_cases hs : Group.IsSolvable (thompsonImage U)
  · obtain ⟨A,hAJ,hn,hsub,he,_,_,hN⟩ := solvable_reduced_thompson_factor U hD
      hr.quotient_pCore_eq_bot hne hs
    exact ⟨A,hAJ,hn,hsub,Or.inl he,hN⟩
  · obtain ⟨C,hCJ,_,_,hn,_,_,_,he⟩ :=
      nonsolvable_reduced_thompson_normal_factor T hE faithful I hTI hI hD U hr hs
    let : (C.map (actionMk U)).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
    exact ⟨C.map (actionMk U),map_mono hCJ,inferInstance,
      (inferInstance : (C.map (actionMk U)).Normal).isSubnormal,
      Or.inr ⟨inferInstance,he⟩,fun _ _ => le_normalizer_of_normal⟩

open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- Select the source small factor without a solvability premise, retaining
the original geometry, cubic, faithful nine-group and generation clauses.
Normality in the nonsolvable branch and both actor normalizations are proved. -/
theorem local_nonnormal_component_weakClosure_factors
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
                normalizer (((F.Li L 1).subgroupOf I₀).map q : Set _) ∧
              ∃ A : Subgroup _, A ≤ (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ∧
                (A.subgroupOf ((elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q)).Normal ∧
                A.IsSubnormal ∧
                (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
                  A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
                    Nonempty (A ≃* Matrix.PSL3Two.PSL))) ∧
                pResidual 2 (I₀ ⧸ centralizer
                  ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀)) ≤ normalizer (A : Set _) ∧
                ((F.Li L 1).subgroupOf I₀).map q ≤ normalizer (A : Set _) ∧
                ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                  normalizer (A : Set _) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot⟩ :=
    local_nonnormal_component_weakClosure_thompson d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα B
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := B ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  refine ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot,?_⟩
  let : IsElementaryAbelian 2 (W.subgroupOf I₀) := hred.elementary
  have hTI : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  have hWI : W ≤ I₀ := hVIW.trans (hWR.trans (hRT.trans hTI))
  have hIcore : I₀ ∈ Chapter1.H G := by
    have hw : W ≤ I₀.pCoreIn 2 := by
      have hw₀ : W.subgroupOf I₀ ≤ pCore 2 I₀ := hred.le_pCore
      simpa only [pCoreIn,map_subgroupOf_eq_of_le hWI] using
        map_mono (f := I₀.subtype) hw₀
    intro hz
    have hp : F.Vi 1 ⊔ c.Zα = ⊥ := bot_unique ((hPVI.trans hw).trans hz.le)
    rw [hp,card_bot] at hfour
    norm_num at hfour
  obtain ⟨A,hAJ,hAn,hAsub,hmodel,hAN⟩ := reduced_thompson_small_factor
    T (d.qtke.evenCharacteristic T) faithful I₀ hTI hIcore hsqtk
    (W.subgroupOf I₀) hred hJplus
  have hLI : F.Li L 1 ≤ I₀ := le_sup_left.trans le_sup_left
  let e := subgroupOfEquivOfLe hLI
  have hpL : IsPPerfect 2 ((F.Li L 1).subgroupOf I₀) :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  have hpLplus : IsPPerfect 2 (((F.Li L 1).subgroupOf I₀).map q) :=
    hpL.of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  have hpNine : IsPPerfect 2 (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) := by
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (_ ⧸ N) = 1
    apply htwo.card_eq_or_dvd.resolve_right
    intro hd
    have hh := hd.trans N.card_quotient_dvd_card
    rw [hplus] at hh
    norm_num at hh
  exact ⟨A,hAJ,hAn,hAsub,hmodel,hAN _ (isPPerfect_pResidual 2),
    hAN _ hpLplus,hAN _ hpNine⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
