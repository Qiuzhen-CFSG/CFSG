module
public import CFSG.Quasithin.ChapterA.Section04.Signalizers
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# The original signalizer-chain theorem A.4.10

Let X≤Y and retain the original Sylow subgroup T and the literal section
centralizer S=C_T(X/O₂(X)). The normalizer-Sylow hypothesis makes S the
maximal X-signalizer by A.4.2. The core R=O₂(YT) joins S as a signalizer,
so R≤S. Since characteristic two survives adjoining the normalizing two-group,
Ω₁(Z(S))≤Ω₁(Z(R)); the actual commutator modules therefore satisfy
V(X,S)≤V(Y,R). Finally A.4.8 transfers nontriviality from V(X) to V(X,S)
and then to V(Y). No chain-module or faithful-type conclusion is assumed.

Source: Aschbacher--Smith, Lemma A.4.10, printed p.60.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterA.Section04.SourceChains
variable {G : Type*} [Group G] [Finite G]

private theorem section_isMaximal (X Y T : Subgroup G) (hXY : X ≤ Y)
    (hX : IsPPerfect 2 X)
    (hSyl : Chapter1.IsSylowIn 2 (T ⊓ normalizer (X : Set G))
      ((Y ⊔ T) ⊓ normalizer (X : Set G))) :
    IsMaximalTwoSignalizer X ((Y ⊔ T) ⊓ normalizer (X : Set G))
      (twoSectionCentralizer X T) := by
  let N := (Y ⊔ T) ⊓ normalizer (X : Set G)
  let U := T ⊓ normalizer (X : Set G)
  let J := X ⊔ U
  have hXN : X ≤ N := le_inf (hXY.trans le_sup_left) X.le_normalizer
  have hUN : U ≤ N := le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hJN : J ≤ N := sup_le hXN hUN
  have hNX : N ≤ normalizer (X : Set G) := inf_le_right
  have hsub : (X.subgroupOf N).IsSubnormal := (normal_subgroupOf_of_le_normalizer hNX).isSubnormal
  obtain ⟨P,hP⟩ := hSyl
  have hm := normal_sylow_core_isMaximal X N hXN hNX hX P
  rw [hP] at hm
  change IsMaximalTwoSignalizer X N (J.pCoreIn 2) at hm
  have hm0 := (isMaximalTwoSignalizer_iff _ _ _).mp hm
  obtain ⟨PJ,hPJ⟩ := (show Chapter1.IsSylowIn 2 U N from ⟨P,hP⟩).restrict
    (show U ≤ J from le_sup_right) hJN
  have hRU : J.pCoreIn 2 ≤ U := (pCoreIn_le_sylow J PJ).trans_eq hPJ
  have hSX : J.pCoreIn 2 ≤ twoSectionCentralizer X T := by
    apply (le_twoSectionCentralizer_iff _ _ _).mpr
    exact ⟨hRU.trans inf_le_left,hRU.trans inf_le_right,
      signalizer_commutator_le_pCore X N _ hXN hsub hX hm0.1⟩
  have hQX : X.pCoreIn 2 ≤ J.pCoreIn 2 := actor_core_le_maximal_signalizer X N _ hXN hm
  have hS : IsTwoSignalizer X N (twoSectionCentralizer X T) := by
    apply signalizer_of_le_twoSectionCentralizer
    · have hUp : IsPGroup 2 U := by
        have hh := P.isPGroup'.map N.subtype
        change IsPGroup 2 ((P : Subgroup N).map N.subtype) at hh
        change IsPGroup 2 (T ⊓ normalizer (X : Set G) : Subgroup G)
        rwa [hP] at hh
      exact hUp.to_le (le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _))
    · exact (le_twoSectionCentralizer_iff _ _ _).mpr
        ⟨(le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _)).trans hUN,
          twoSectionCentralizer_le_normalizer _ _,
          ((le_twoSectionCentralizer_iff X T _).mp le_rfl).2.2⟩
    · exact hQX.trans hSX
  have he : J.pCoreIn 2 = twoSectionCentralizer X T :=
    le_antisymm hSX (hm0.2 _ hS hSX)
  exact he ▸ hm

theorem source_A410 (X Y T : Subgroup G) (hXY : X ≤ Y)
    (hX : IsSignalizerType X) (hY : IsSignalizerType Y)
    (hTY : T ≤ normalizer (Y : Set G)) (hT : Chapter1.IsSylowIn 2 T (Y ⊔ T))
    (hcore : (Y ⊔ T).pCoreIn 2 ≤ T ⊓ normalizer (X : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (T ⊓ normalizer (X : Set G))
      ((Y ⊔ T) ⊓ normalizer (X : Set G))) :
    IsMaximalTwoSignalizer X ((Y ⊔ T) ⊓ normalizer (X : Set G))
      (twoSectionCentralizer X T) ∧
    signalizerModule X (twoSectionCentralizer X T) ≤ signalizerModule Y ((Y ⊔ T).pCoreIn 2) ∧
    (IsFaithfulSignalizerType X → IsFaithfulSignalizerType Y) := by
  let M := Y ⊔ T
  let N := M ⊓ normalizer (X : Set G)
  let S := twoSectionCentralizer X T
  let R := M.pCoreIn 2
  have hXM : X ≤ M := hXY.trans le_sup_left
  have hXN : X ≤ N := le_inf hXM X.le_normalizer
  have hNX : N ≤ normalizer (X : Set G) := inf_le_right
  have hsub : (X.subgroupOf N).IsSubnormal := (normal_subgroupOf_of_le_normalizer hNX).isSubnormal
  have hs := section_isMaximal X Y T hXY hX.2.1 hSyl
  have hs0 := (isMaximalTwoSignalizer_iff _ _ _).mp hs
  have hSN : S ≤ N := hs0.1.le
  have hSR : S ≤ normalizer (R : Set G) :=
    hSN.trans (inf_le_left.trans (M.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore M)))
  have hXR : X ≤ normalizer (R : Set G) :=
    hXM.trans (M.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore M))
  have hRS : R ≤ S := by
    have hRN : R ≤ N := le_inf (pCoreIn_le _ _) (hcore.trans inf_le_right)
    have hjoin : IsTwoSignalizer X N (R ⊔ S) := by
      apply (isTwoSignalizer_iff _ _ _).mpr
      exact ⟨sup_le hRN hSN,(isPGroup_pCoreIn 2 M).to_sup_of_normal_left' hs0.1.isPGroup hSR,
        (le_inf hXR hs0.1.normalizes).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)⟩
    exact le_sup_left.trans (hs0.2 _ hjoin le_sup_right)
  have hYM : Y ≤ M := le_sup_left
  have hMY : M ≤ normalizer (Y : Set G) := sup_le Y.le_normalizer hTY
  have hYsub : (Y.subgroupOf M).IsSubnormal := (normal_subgroupOf_of_le_normalizer hMY).isSubnormal
  have hRY : IsTwoSignalizer Y M R := (isTwoSignalizer_iff _ _ _).mpr
    ⟨pCoreIn_le _ _,isPGroup_pCoreIn _ _,hYM.trans
      (M.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore M))⟩
  have hQY : Y.pCoreIn 2 ≤ R := pCoreAmbient_mono_of_isSubnormalIn Y M 2 hYM hYsub
  have hMYcore : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    apply centralizer_pCore_sup_le 2 Y T
    · rw [← hY.2.2]
      exact centralizer_generalizedFitting_le Y
    · exact (Chapter1.isSylowIn_iff.mp hT).1
    · exact hTY
  have hOmega : omegaOneCenterAmbient S ≤ omegaOneCenterAmbient R := by
    intro z hz
    obtain ⟨hzS,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    have hzM : z ∈ M := hSN hzS |>.1
    have hzR : z ∈ R := by
      have hc : (⟨z,hzM⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
        apply mem_centralizer_iff.mpr
        intro r hr
        exact Subtype.ext (hzC r (hRS (mem_map_of_mem M.subtype hr)))
      exact mem_map_of_mem M.subtype (hMYcore hc)
    exact (mem_omegaOneCenterAmbient_iff R z).mpr
      ⟨hzR,hz2,fun r hr => hzC r (hRS hr)⟩
  have hmod : signalizerModule X S ≤ signalizerModule Y R := by
    rw [signalizerModule_eq_commutator_omegaCenter,signalizerModule_eq_commutator_omegaCenter]
    exact commutator_mono hXY hOmega
  refine ⟨hs,hmod,fun hf => ⟨hY,?_⟩⟩
  have hQX : X.pCoreIn 2 ≤ S := actor_core_le_maximal_signalizer X N S hXN hs
  have hcomm : ⁅X,S⁆ ≤ X.pCoreIn 2 := signalizer_commutator_le_pCore X N S hXN hsub hX.2.1 hs0.1
  have hne := (signalizerModule_ne_bot_iff_intrinsic X S hX.2.1 hs0.1.isPGroup
    hs0.1.normalizes hQX hcomm).mpr hf.2
  have hle := signalizerModule_le_intrinsicModule Y R hY.2.1 hRY.normalizes hQY
    (signalizer_commutator_le_pCore Y M R hYM hYsub hY.2.1 hRY)
  intro he
  exact hne (eq_bot_iff.mpr ((hmod.trans hle).trans he.le))

end CFSG.Quasithin.ChapterA.Section04.SourceChains
