module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherComponents
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import Theory.GroupAction.BinaryFullCommutator

/-!
# The faithful component chain in the higher-dimensional rigidity argument

Let Y=O²(N_L(U∩V)). Its full action on W=U∩V gives [Y,W]=W, so W
lies in O₂(Y). The marked quotient calculation identifies that core with
the action kernel on W. Hence W lies in Ω₁Z(O₂(Y)), and commutator
generation puts W in the intrinsic signalizer module of Y. In particular
Y belongs to the genuine faithful local-component family.

The proved faithful-chain theorem promotes this to every containing local
component. Combining the normal component in N_G(C_T(U)) with finite
maximality constructs the exact source chain Y≤Y_R≤Y₀, where Y_R is normal
in that normalizer and Y₀ is maximal in the full local family and faithful.
No abstract component label or assumed normality of Y is used. The component
sieve proving Y_R=Y, and the subsequent tensor and dimension arguments,
remain with the final owner qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.25, printed p.805, using 1.2.4 and 1.2.9 on pp.505--507.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U H P : Subgroup G} {d : ℕ}

omit [Finite G] in
private theorem hyperplane_card_gt_two (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : 2 < Nat.card (U ⊓ V : Subgroup G) := by
  rw [C.hyperplane]
  exact lt_of_eq_of_lt (by decide : 2 = 2^1) (pow_lt_pow_right₀ (by decide) (by omega))

/-- The literal residual moves the whole original hyperplane. -/
theorem residual_hyperplane_commutator (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : ⁅rigidityHyperplaneResidual L U V, U ⊓ V⁆ = U ⊓ V := by
  let := C.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left))
      (inclusion_injective _)
  exact BinarySubspaceResidual.commutator_eq_of_full _ _
    ((map_subtype_le _).trans inf_le_right) (hyperplane_card_gt_two C hd)
    (residualHyperplaneAction_surjective D A C hd)

/-- The hyperplane lies in the two-core of the residual, using actual
commutator generation rather than an arbitrary natural-module tag. -/
theorem hyperplane_le_residual_core (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : U ⊓ V ≤ (rigidityHyperplaneResidual L U V).pCoreIn 2 := by
  let Y := rigidityHyperplaneResidual L U V
  let F := hyperplaneNormalizer L U V
  have hWY : U ⊓ V ≤ Y := by
    rw [← residual_hyperplane_commutator D A C hd]
    apply le_normalizer_iff_commutator_le_left.mp
    have hWF : U ⊓ V ≤ F := le_inf (inf_le_right.trans D.le_component) (U ⊓ V).le_normalizer
    exact hWF.trans (F.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F (pResidual 2 F)))
  exact le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (inf_le_left.trans C.core_le_sylow)) hWY
    ((map_subtype_le _).trans inf_le_right)

/-- The kernel identification makes the original hyperplane central in O₂(Y). -/
theorem residual_core_centralizes_hyperplane (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) :
    (rigidityHyperplaneResidual L U V).pCoreIn 2 ≤ centralizer ((U ⊓ V : Subgroup G) : Set G) := by
  rintro z ⟨y,hy,rfl⟩ w hw
  have hk := (residualHyperplaneAction_ker D A C hd).symm.le hy
  have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp hk) (⟨w,hw⟩ : (U ⊓ V : Subgroup G))
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm

/-- The hyperplane is contained in the intrinsic signalizer module of Y. -/
theorem hyperplane_le_intrinsic_module (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : U ⊓ V ≤ intrinsicSignalizerModule (rigidityHyperplaneResidual L U V) := by
  let := C.elementary
  have hWQ := hyperplane_le_residual_core D A C hd
  have hWZ := le_centralizer_iff.mp (residual_core_centralizes_hyperplane D A C hd)
  have hWO : U ⊓ V ≤ Stellmacher.omegaOneCenterAmbient ((rigidityHyperplaneResidual L U V).pCoreIn 2) := by
    intro w hw
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hWQ hw,elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw.1,hWZ hw⟩
  rw [intrinsicSignalizerModule,signalizerModule_eq_commutator_omegaCenter,
    ← residual_hyperplane_commutator D A C hd]
  exact commutator_mono le_rfl hWO

/-- Y belongs to the faithful local family under the original ambient hypotheses. -/
theorem residual_mem_faithful_family
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : rigidityHyperplaneResidual L U V ∈ MainForward.faithfulLocalComponents T := by
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (h.simpleQTKE.evenCharacteristic T)).mpr
  refine ⟨residual_mem_local_family D A C hd (((structural G T L h).2.2 V D).1),?_⟩
  apply ne_bot_of_le_ne_bot _ (hyperplane_le_intrinsic_module D A C hd)
  exact (one_lt_card_iff_ne_bot _).mp (lt_trans (by decide : 1 < 2) (hyperplane_card_gt_two C hd))

/-- Any local component containing the original residual is faithful. -/
theorem containing_component_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K : Subgroup G} (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    K ∈ MainForward.faithfulLocalComponents T :=
  Chapter1.Section02.Adequate.faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T)
    (residual_mem_faithful_family h D structural A C hd) hK hYK

/-- The source component chain Y≤Y_R≤Y₀, with relative normality of Y_R
and genuine maximal faithful-family membership of Y₀. -/
theorem source_containing_component_chain
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
      (K.subgroupOf (normalizer
        (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
        normalizer (K : Set G) ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
      K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ := by
  obtain ⟨K,hKN,hK,hYK,hn,hlocal⟩ := exists_normal_containing_component h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone) hd
  obtain ⟨K₀,hK₀,hKK₀⟩ := Chapter1.exists_mem_LStar_ge hlocal
  have hf := containing_component_faithful h D structural A C hd hK₀.1 (hYK.trans hKK₀)
  exact ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K₀).mp hf).2⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
