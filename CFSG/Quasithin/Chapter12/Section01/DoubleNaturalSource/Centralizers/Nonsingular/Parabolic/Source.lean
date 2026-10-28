module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.SporadicSource
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonquasisimpleFitting
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.CComponent.FittingNormalizerQuotient
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension

/-!
# The nonnormal nonsingular branch and its original star module

The normal containing C-component of C_G(w) strictly contains the point
residual and escapes C_M(w). If its two-core quotient were not quasisimple,
the proved C.2.6 fitting control would place its Fitting preimage in C_M(w).
That preimage normalizes the original residual, whose quotient is simple;
the Fitting-normalizer criterion gives a contradiction. This constructs
all of the genuine C.2.7 input with normality relative to C_G(w).

The existing C.2.7(1–2) proofs then supply the kernel and offender clauses.
Radical saturation and characteristic two place the original T-fixed line
in the Sylow-fixed part of the literal omega-center. The residual retains
its L_(n-1)(2) quotient and its relative normality under the same star map:
the restricted kernel is solvable, hence lies in its two-core.

The final theorem applies these results to nonsingular centralizer control
and degree-five zeroth closure. It still requires the three ordinary-component
exclusions and the parabolic fixed-space argument. The latter concerns the
Sylow-fixed part, not centralization of the entire natural-plus-dual module.
No universal C.2.7 Source or EarlierMSClassifications premise is instantiated.
The remaining arguments belong to qt-d-double-natural-centralizers; independent
pure fusion belongs to qt-d-double-natural-pure-fusion, with final assembly
at qt-d-1222-double-natural. This does not complete source 12.1.1.

Source: Aschbacher–Smith 12.1.1, printed pp.788–789; C.2.6–7, pp.145–147;
1.2.1(4), p.505. The original W and its moving subgroup remain distinct.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
open BinaryNaturalDual.ModelOrbits.AutomorphismModel BinaryLinear.OuterCyclic
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem residual_quotient_quasisimple
    {n : ℕ} (B : DoubledBranch T L V n)
    [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
    (S : B.SourceModel) (w : componentOrbit V (T : Subgroup G))
    (hw : B.AdaptedPoint S w) :
    IsQuasisimple (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) := by
  obtain ⟨e⟩ := (S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).2
  have hn : 3 ≤ n-1 := by have := B.degree; omega
  let : IsQuasisimple (LinearGroup (n-1)) :=
    IsQuasisimple.of_mulEquiv
      (innerEquiv (by omega : 0 < n-1)).symm
      (hG := (inner_isComponent hn).2)
  exact IsQuasisimple.of_mulEquiv
    (e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n-1))).symm

/-- The nonnormal branch has an escaping normal C-component with quasisimple two-core quotient. -/
theorem doubleNatural_adapted_nonnormal_containing_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∃ K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w < K ∧
        ¬ K ≤ B.localPointCentralizer w ∧
        generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hnon
  let H := B.pointCentralizer w
  let M := B.localPointCentralizer w
  let A := B.pointResidual w
  obtain ⟨K,⟨hK,hAK,hn⟩,_⟩ := D.doubleNatural_adapted_containing_cComponent h B S w hw
  have hAM : A ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hne : A ≠ K := by
    intro he
    apply hnon
    change (A.subgroupOf H).Normal
    rw [he]
    exact hn
  have hout : ¬ K ≤ M := by
    intro hKM
    have he := (S.nonsingular_residual_local_cComponent w hw.nonsingular).eq_of_le
      (hK.2.subgroupOf_of_le hKM inf_le_right) (comap_mono hAK)
    change A.subgroupOf M = K.subgroupOf M at he
    have he' : A = K := by
      simpa only [map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le hKM] using
        congrArg (map M.subtype) he
    exact hne he'
  have hfit : generalizedFitting K = pCore 2 K := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hK.1)).mp
    apply subnormal_core_selfCentralizing _ _ hK.2.subnormal
    rw [←hc]
    exact centralizer_generalizedFitting_le H
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := by
    by_contra hnot
    have hfitM := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
      (D.doubleNatural_adapted_pushingUpSetup h B S w hw) hK hfit
      ((normal_subgroupOf_iff_le_normalizer hK.1).mp hn) hnot
    let A₀ := A.subgroupOf K
    let eA := subgroupOfEquivOfLe hAK
    let := residual_quotient_quasisimple B S w hw
    have hAq : IsQuasisimple (A₀ ⧸ pCore 2 A₀) :=
      IsQuasisimple.of_mulEquiv
        (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).symm
    have htop : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
    apply hnot (quasisimple_quotient_of_fitting_normalizes htop A₀ hAq ?_)
    rw [←subgroupOf_normalizer_eq hAK]
    intro k hk
    exact B.localPointCentralizer_normalizes_residual w
      (hfitM (mem_map_of_mem K.subtype hk))
  exact ⟨K,hK,hn,lt_of_le_of_ne hAK hne,hout,hfit,hq⟩

/-- Every genuine C.2.7 input follows from the characteristic-two nonnormal branch. -/
theorem doubleNatural_adapted_nonnormal_C27_input
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∃ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal ∧
        B.pointResidual w < K ∧
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w)
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) (B.localPointCentralizer w) K := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn
  obtain ⟨K,hK,hKn,hAK,ho,hf,hq⟩ :=
    D.doubleNatural_adapted_nonnormal_containing_quotient h B S w hw hc hn
  refine ⟨K,hKn,hAK,⟨D.doubleNatural_adapted_pushingUpSetup h B S w hw,hK,hq,hf,ho,?_⟩⟩
  exact (D.doubleNatural_core_le_pointCentralizer h B w).trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)

/-- The original T-fixed line lies in the C_T(w)-fixed part of the actual C.2.7 omega-center. -/
theorem doubleNatural_adapted_fixedLine_le_C27_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), ∀ K : Subgroup G,
      (K.subgroupOf (B.pointCentralizer w)).Normal →
      Input KnownSimple.IsKnownSimple (B.pointCentralizer w)
        ((L ⊔ (T : Subgroup G)).pCoreIn 2) (B.localPointCentralizer w) K →
      B.fixedLine ≤ (starV K ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
        (K ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).subtype ⊓
          centralizer (B.pointSylow w : Set G) := by
  let := D.doubledOrbit_elementary h
  intro w K hn hi
  let := hn
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := K ⊔ Q
  have hcore : J.pCoreIn 2 ≤ Q := ChapterC.C27Source.source_joinCore_le_radical hi
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact inf_le_left
  have hWQ : componentOrbit V (T : Subgroup G) ≤ Q := by
    change componentOrbit V (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact le_inf (D.doubledOrbit_E322 h).le_sylow
      (fun x hx y hy => congrArg Subtype.val (mul_comm
        (⟨y,hy⟩ : componentOrbit V (T : Subgroup G)) ⟨x,hx⟩))
  have hJc := centralizer_pCore_sup_le 2 K Q
    (by rw [←hi.fitting]; exact centralizer_generalizedFitting_le K)
    (isPGroup_pCoreIn 2 _) hi.normalizes
  apply le_inf ?_ (inf_le_right.trans (centralizer_le inf_le_left))
  intro z hz
  let zJ : J := ⟨z,mem_sup_right (hWQ hz.1)⟩
  have hzC : zJ ∈ centralizer (pCore 2 J : Set J) := by
    intro a ha
    exact Subtype.ext (hz.2 a (hQT (hcore (mem_map_of_mem J.subtype ha))))
  refine ⟨zJ,?_,rfl⟩
  change zJ ∈ omegaOneCenterAmbient (pCore 2 J)
  exact (mem_omegaOneCenterAmbient_iff _ zJ).mpr
    ⟨hJc hzC,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz.1),
      fun a ha => hzC a ha⟩

/-- The literal residual star image is relatively normal and retains its original simple two-core quotient. -/
theorem doubleNatural_adapted_C27_residual_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
      Input KnownSimple.IsKnownSimple (B.pointCentralizer w)
        ((L ⊔ (T : Subgroup G)).pCoreIn 2) (B.localPointCentralizer w) K →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      let A := starImage K Q (B.pointResidual w)
      (A.subgroupOf (starM K Q (B.localPointCentralizer w))).Normal ∧
      Nonempty ((A ⧸ pCore 2 A) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hAK hi
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := K ⊔ Q
  let A := B.pointResidual w
  let M := B.localPointCentralizer w
  let Astar := starImage K Q A
  let q := QuotientGroup.mk' (starKernel K Q)
  have hAM : A ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hAJ : A ≤ J := hAK.trans le_sup_left
  have hstar : Astar ≤ starM K Q M := map_mono (comap_mono (le_inf hAM hAK))
  refine ⟨(normal_subgroupOf_iff_le_normalizer hstar).mpr ?_,?_⟩
  · rintro _ ⟨m,hm,rfl⟩
    apply le_normalizer_map q
    apply mem_map_of_mem q
    rw [←subgroupOf_normalizer_eq hAJ]
    exact B.localPointCentralizer_normalizes_residual w hm.1
  · let eA := subgroupOfEquivOfLe hAJ
    let f : A →* Astar := (q.subgroupMap (A.subgroupOf J)).comp eA.symm.toMonoidHom
    have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp eA.symm.surjective
    let i : f.ker →* (toStarImage K Q).ker :=
      ((inclusion hAK).comp f.ker.subtype).codRestrict _ (by
        intro a
        apply Subtype.ext
        have ha : f a.val = 1 := a.property
        exact congrArg (fun x : Astar => (x : StarQuotient K Q)) ha)
    have hinj : Function.Injective i := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : (toStarImage K Q).ker => ((x : K) : G)) he
    let := ChapterC.C27Source.toStarImage_ker_solvable_from_source hi
    let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hinj
    let := (S.nonsingular_residual_local_cComponent w hw.nonsingular).perfect
    let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hAM).toMonoidHom)
      (subgroupOfEquivOfLe hAM).surjective
    obtain ⟨e⟩ := (S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).2
    have hn : 3 ≤ n-1 := by have := B.degree; omega
    let eL := e.trans (projectiveEquivLinear (by omega : 0 < n-1))
    let := linear_simple hn
    let : IsSimpleGroup (A ⧸ pCore 2 A) := eL.isSimpleGroup
    have hk : f.ker ≤ pCore 2 A := by
      rw [←PerfectCoreTwoExtension.radical_eq_core]
      exact le_solvableRadical _ inferInstance inferInstance
    exact ⟨(f.pCoreQuotientEquiv hf (pCore_isPGroup.to_le hk)).symm.trans e⟩

/-- The nonnormal branch supplies the original star kernel, offenders, fixed line and residual marking. -/
theorem doubleNatural_adapted_nonnormal_source_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∃ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal ∧
        B.pointResidual w < K ∧
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K ∧
        KernelConclusion K Q ∧ OffenderConclusion K Q ∧
        B.fixedLine ≤ (starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) ∧
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal ∧
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn
  obtain ⟨K,hKn,hAK,hi⟩ := D.doubleNatural_adapted_nonnormal_C27_input h B S w hw hc hn
  obtain ⟨hk,ho⟩ := ChapterC.C27Source.kernel_offender_from_source hi
  obtain ⟨hAn,hAq⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hAK.le hi
  exact ⟨K,hKn,hAK,hi,hk,ho,
    D.doubleNatural_adapted_fixedLine_le_C27_module h B w K hKn hi,hAn,hAq⟩

/-- Apply the remaining component exclusions and parabolic Sylow-fixed-space argument to the actual centralizer and degree-five closure consumers. -/
theorem doubleNatural_nonsingular_controls_of_three_models_C27_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        ((n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal →
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hmodels hparabolic
  apply D.doubleNatural_nonsingular_controls_of_three_models_parabolic_of_many
    h hmany B hmodels
  intro S w hw hc hn hout
  obtain ⟨K,hKn,hAK,hi,hk,ho,hline,hAn,hAq⟩ :=
    D.doubleNatural_adapted_nonnormal_source_data h B S w hw hc hn
  exact (hparabolic S w hw hc hn hout K hKn hAK hi hk ho hAn hAq).trans
    (centralizer_le hline)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
