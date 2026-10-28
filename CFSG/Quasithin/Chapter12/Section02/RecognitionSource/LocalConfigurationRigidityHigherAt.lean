module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherNoncentral
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityParabolicAt

/-!
# The containing-component sieve at the original G and T

The containing-component catalogue applies 12.2.2 to K₀ in the same G,T.
Use the local structural and seven-module inputs there; all other structural
uses normalize the original V. Reuse the binary, A₇ and prime-linear model
calculations and retain the actual component inclusions and quotient maps.

These are additive specializations of the corresponding rigidity modules;
public results independent of the universal inputs are reused directly.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.804–806
(PDF pp.821–823), with 12.2.2(3) and A.3.12 for containing components.
-/

public noncomputable section

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Equality in the literal radical quotient lifts to the original subgroups. -/
theorem residual_eq_containing_of_image_eq_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (he : ThreeRigidity.image T U (rigidityHyperplaneResidual L U V) =
      ThreeRigidity.image T U K) : rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S := T.subtype (sylow_normalizes_sectionRadical C)
  have hlocal : (rigidityHyperplaneResidual L U V).subgroupOf N ∈ Chapter1.L N S :=
    (Chapter1.mem_LIn_iff_subgroupOf (sylow_normalizes_sectionRadical C)
      B.residual_normalizes).mp
      ⟨B.residual_normalizes,residual_mem_local_family D A C hd
        (((structural L h).2.2 V D).1)⟩
  have hh := local_cComponent_eq_of_map_eq hlocal.1 hK (comap_mono hYK)
    (quotient R) (show (quotient R).ker ≤ (S : Subgroup N) from by
      change (QuotientGroup.mk' (R.subgroupOf N)).ker ≤ _
      rw [QuotientGroup.ker_mk']
      exact comap_mono (show R ≤ (T : Subgroup G) from inf_le_left)) he
  have hm := congrArg (map N.subtype) hh
  change ((rigidityHyperplaneResidual L U V).subgroupOf N).map N.subtype =
    (K.subgroupOf N).map N.subtype at hm
  rw [map_subgroupOf_eq_of_le (show rigidityHyperplaneResidual L U V ≤ N from B.residual_normalizes),
    map_subgroupOf_eq_of_le (show K ≤ N from hKN)] at hm
  exact hm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U H P : Subgroup G} {d : ℕ}

/-- The actual containing C-component in N_G(C_T(U)), normal in that
normalizer. Equality with Y is the remaining component-sieve obligation. -/
theorem exists_normal_containing_component_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    ∃ K : Subgroup G,
      K ≤ normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
      (K.subgroupOf (normalizer
        (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
        normalizer (K : Set G) ∧ K ∈ Chapter1.L G (T : Subgroup G) := by
  let Y := rigidityHyperplaneResidual L U V
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let N := normalizer (R : Set G)
  have hTN : (T : Subgroup G) ≤ N :=
    (le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hRN : R ≤ N := R.le_normalizer
  have hRne : R ≠ ⊥ := ne_bot_of_le_ne_bot
    (C.core_ne_bot (by omega : 2 ≤ d)) (le_inf C.core_le_sylow (by
      let := C.elementary
      exact le_centralizer U))
  have hNH : N ∈ Chapter1.H G := ne_bot_of_le_ne_bot hRne
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left) hRN le_rfl)
  have hTV := ((structural L h).2.2 V D).1
  have hYL := residual_mem_local_family D A C hd hTV
  have hYN : Y ≤ N := B.residual_normalizes
  let S := T.subtype hTN
  have hlocal : Y.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (Chapter1.mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN,hYL⟩
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono (sylow_normalizes_residual D C hTV)
  obtain ⟨K,⟨hK,hYK,hn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hNH) S hlocal hSY
  let K' := K.map N.subtype
  have hKN : K' ≤ N := map_subtype_le _
  have he : K'.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  have hcmp : (K'.subgroupOf N).IsCComponent := he.symm ▸ hK
  have hnorm : N ≤ normalizer (K' : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKN).mp (he.symm ▸ hn)
  refine ⟨K',hKN,hcmp,?_,hnorm,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hYN] using map_mono (f := N.subtype) hYK
  · exact Chapter1.mem_L_of_cComponent hNH
      ⟨S,by simp only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN]⟩ hKN hcmp

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The hyperplane-action kernel lies in the original radical times V. -/
theorem residual_core_le_radical_sup_chosen_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    (rigidityHyperplaneResidual L U V).pCoreIn 2 ≤ sectionRadical T U ⊔ V := by
  let Y := rigidityHyperplaneResidual L U V
  let J := Y ⊔ (T : Subgroup G)
  have hTY := sylow_normalizes_residual D C (((structural L h).2.2 V D).1)
  have hcoreT : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes (show Y ≤ J from le_sup_left)
      (sup_le Y.le_normalizer hTY)).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hc := le_inf hcoreT (residual_core_centralizes_hyperplane D A C hd)
  rw [RigidityKernel.hyperplane_centralizer_eq_core_sup_kernel_at h D structural A C,
    B.kernel_split] at hc
  exact hc.trans (sup_le (le_sup_left.trans B.centralizer_split.symm.le |>.trans le_sup_left)
    (sup_le le_sup_right (le_sup_right.trans B.centralizer_split.symm.le |>.trans le_sup_left)))

/-- Modulo R the hyperplane-action kernel is central in the residual image. -/
theorem residual_core_commutator_le_radical_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    ⁅(rigidityHyperplaneResidual L U V).pCoreIn 2,rigidityHyperplaneResidual L U V⁆ ≤
      sectionRadical T U := by
  let R := sectionRadical T U
  let Y := rigidityHyperplaneResidual L U V
  have hVR : V ≤ normalizer (R : Set G) := D.le_sylow.trans (sylow_normalizes_sectionRadical C)
  have hVY : ⁅V,Y⁆ ≤ R := (commutator_le_of_normalized_index_two V (U ⊓ V) Y
    inf_le_right (RigidityResidual.hyperplane_index A C)
    ((map_subtype_le _).trans (inf_le_left.trans D.normalizes))
    ((map_subtype_le _).trans inf_le_right)).trans
      (le_inf (inf_le_left.trans C.core_le_sylow) (by
        let := C.elementary
        exact inf_le_left.trans (le_centralizer U)))
  apply commutator_le.mpr
  intro x hx y hy
  have hxRV := residual_core_le_radical_sup_chosen_at h D structural A C B hd hx
  have hp : x ∈ (R : Set G) * (V : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left R V hVR]
  obtain ⟨r,hr,v,hv,rfl⟩ := hp
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact R.mul_mem (R.mul_mem (R.mul_mem hr
    (hVY (commutator_mem_commutator hv hy))) (R.inv_mem hr))
    (le_normalizer_iff_commutator_le_left.mp B.residual_normalizes
      (commutator_mem_commutator hr hy))

/-- The literal Y-image in N(R)/R is a perfect central cover of Aut(U ∩ V),
and hence quasisimple. No residual-normality assumption is used. -/
theorem residual_image_quasisimple_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    IsQuasisimple (ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)) := by
  let Y := rigidityHyperplaneResidual L U V
  let R := sectionRadical T U
  let f : Y →* NormalizerQuotient R := (quotient R).comp (inclusion B.residual_normalizes)
  let a := residualHyperplaneAction L U V
  have hka : f.ker ≤ a.ker := by
    intro y hy
    have hyr : (y : G) ∈ R :=
      (QuotientGroup.eq_one_iff (⟨y,B.residual_normalizes y.property⟩ : normalizer (R : Set G))).mp
        (MonoidHom.mem_ker.mp hy)
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hyr.2 w w.property.1).symm
  let g : (Y ⧸ f.ker) →* MulAut (U ⊓ V : Subgroup G) := QuotientGroup.lift f.ker a hka
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _
    (residualHyperplaneAction_surjective D A C hd) hka
  have hgc : g.ker ≤ center (Y ⧸ f.ker) := by
    intro x hx
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective f.ker x
    have hy : y ∈ pCore 2 Y := by
      rw [← residualHyperplaneAction_ker D A C hd]
      exact hx
    apply mem_center_iff.mpr
    intro z
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective f.ker z
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    exact residual_core_commutator_le_radical_at h D structural A C B hd
      (commutator_mem_commutator (mem_map_of_mem Y.subtype hy) z.property)
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural L h).2.2 V D).1))
  let := (hyperplaneAut_simple_perfect C hd).1
  let := (hyperplaneAut_simple_perfect C hd).2
  have hc : center (MulAut (U ⊓ V : Subgroup G)) = ⊥ := by
    rcases (inferInstance : (center (MulAut (U ⊓ V : Subgroup G))).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple (MulAut (U ⊓ V : Subgroup G)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (Y ⧸ f.ker) := (show PerfectCentralCovering.Cover (Y ⧸ f.ker)
    (MulAut (U ⊓ V : Subgroup G)) from
    { toMonoidHom := g, surjective := hg, isPerfect := inferInstance, ker_le_center := hgc }).isQuasisimple
  have he : f.range = ThreeRigidity.image T U Y := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩
  exact he ▸ IsQuasisimple.of_mulEquiv (QuotientGroup.quotientKerEquivRange f)

/-- The image retains its local C-component condition for the full image Sylow. -/
theorem residual_image_local_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    ThreeRigidity.image T U (rigidityHyperplaneResidual L U V) ∈
      ChapterA.Section03.localCComponents
        (((T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
          (QuotientGroup.mk'_surjective _)) :
            Sylow 2 (NormalizerQuotient (sectionRadical T U))) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S := T.subtype (sylow_normalizes_sectionRadical C)
  have hlocal : (rigidityHyperplaneResidual L U V).subgroupOf N ∈ Chapter1.L N S :=
    (Chapter1.mem_LIn_iff_subgroupOf (sylow_normalizes_sectionRadical C)
      B.residual_normalizes).mp
      ⟨B.residual_normalizes,residual_mem_local_family D A C hd
        (((structural L h).2.2 V D).1)⟩
  let : Group.IsSolvable (quotient R).ker := by
    change Group.IsSolvable (QuotientGroup.mk' (R.subgroupOf N)).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal.1 (quotient R)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Central covers of the ordinary binary containing images cannot enlarge Y. -/
theorem residual_eq_containing_of_binary_central_cover_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {Q : Type*} [Group Q] [Finite Q]
    (f : ThreeRigidity.image T U K →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (ThreeRigidity.image T U K))
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5) (hmodel : ClassicalGroup.IsPSL Q m 2) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  let := residual_image_quasisimple_at h D structural A C B hd
  apply residual_eq_containing_of_image_eq_at h D structural A C B hd hKN hK hYK
  exact ChapterA.Section03.SourceEmbeddings.eq_of_binary_linear_central_cover S
    (residual_image_local_at h D structural A C B hd) (hK.map_quotient (R.subgroupOf N))
    (map_mono (comap_mono hYK)) f hf hk hm hmodel

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The chosen-module action centralizes the containing A₇ image pointwise. -/
theorem chosen_centralizes_alternating_seven_image_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (e : ThreeRigidity.image T U K ≃* alternatingGroup (Fin 7))
    (v : V) :
    quotient (sectionRadical T U) ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩ ∈
      centralizer (ThreeRigidity.image T U K : Set (NormalizerQuotient (sectionRadical T U))) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let Kb := ThreeRigidity.image T U K
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let vN : N := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  let : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Kb.Normal := Subgroup.Normal.map inferInstance (quotient R) (QuotientGroup.mk'_surjective _)
  let := residual_image_quasisimple_at h D structural A C B hd
  let : IsSimpleGroup (Yb ⧸ center Yb) := IsQuasisimple.simple
  let : Nontrivial Yb := (QuotientGroup.mk'_surjective (center Yb)).nontrivial
  have hns : ¬ Group.IsSolvable Yb := Group.IsPerfect.not_isSolvable Yb
  apply AlternatingSeven.SevenFixer.centralizes_of_centralizes_subgroup Kb Yb
    (map_mono (comap_mono hYK)) e hns (seven_dvd_residual_image D A C B hd)
    (quotient R vN) (by exact (normalizer_eq_top Kb).symm ▸ mem_top _)
  rintro yb ⟨y,hy,rfl⟩
  have hc := chosen_residual_actions_commute D A C B v ⟨y,hy⟩
  apply (action_injective R (sectionRadical_selfCentralizing h A C B))
  rw [map_mul,map_mul]
  change R.normalizerMonoidHom y * R.normalizerMonoidHom vN =
    R.normalizerMonoidHom vN * R.normalizerMonoidHom y
  exact hc.eq.symm

/-- The original displacement space is invariant under the containing image,
using the actual commutator map, not its dimension or an abstract module tag. -/
theorem containing_normalizes_hyperplane_of_seven_image_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (e : ThreeRigidity.image T U K ≃* alternatingGroup (Fin 7)) :
    K ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let := D.elementary
  obtain ⟨v,δ,hv,hδ,hδval,_,_⟩ := exists_radical_displacement D A C B
    (((structural L h).2.2 V D).1)
  let vN : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  have hvc := chosen_centralizes_alternating_seven_image_at h D structural A C B hd hYK hn e v
  apply le_normalizer_iff.mpr
  intro k hk w hw
  obtain ⟨r,hr⟩ := hδ ⟨w,hw⟩
  let kN : normalizer (R : Set G) := ⟨k,hKN hk⟩
  have hc : Commute (R.normalizerMonoidHom vN) (R.normalizerMonoidHom kN) := by
    have hh := congrArg (action R (by exact (sectionRadical_selfCentralizing h A C B).symm.le))
      (hvc (quotient R kN) (mem_map_of_mem (quotient R) hk))
    rw [map_mul,map_mul] at hh
    change R.normalizerMonoidHom kN * R.normalizerMonoidHom vN =
      R.normalizerMonoidHom vN * R.normalizerMonoidHom kN at hh
    exact hh.symm
  have he := congrArg (fun r : R => (r : G)) (ConjugationDisplacement.equivariant R vN kN hc r)
  have he' : (δ (R.normalizerMonoidHom kN r) : G) = k * w * k⁻¹ := by
    rw [hδval]
    rw [← ConjugationDisplacement.hom_apply R vN (R.normalizerMonoidHom kN r)]
    rw [he]
    change k * (ConjugationDisplacement.hom R vN r : G) * k⁻¹ = _
    rw [ConjugationDisplacement.hom_apply,← hδval r,hr]
  exact he' ▸ (δ (R.normalizerMonoidHom kN r)).property

/-- The literal A₇ containing image is impossible: its action on the original
hyperplane would surject onto GL₃(2) or GL₄(2), contrary to simplicity and order. -/
theorem no_alternating_seven_containing_image_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G)) :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 := by
  rintro ⟨e⟩
  let R := sectionRadical T U
  let W := U ⊓ V
  let Kb := ThreeRigidity.image T U K
  have hKW := containing_normalizes_hyperplane_of_seven_image_at h D structural A C B hd hKN hYK hn e
  let a : K →* MulAut W := W.normalizerMonoidHom.comp (inclusion hKW)
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨y,hy⟩ := residualHyperplaneAction_surjective D A C hd b
    exact ⟨⟨y,hYK y.property⟩,hy⟩
  let q : K →* NormalizerQuotient R := (quotient R).comp (inclusion hKN)
  have hqrange : q.range = Kb := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      exact k.property
    · intro hx
      exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩
  have hka : q.ker ≤ a.ker := by
    intro k hk
    have hkR : (k : G) ∈ R :=
      (QuotientGroup.eq_one_iff (⟨k,hKN k.property⟩ : normalizer (R : Set G))).mp hk
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hkR.2 w w.property.1).symm
  let g : (K ⧸ q.ker) →* MulAut W := QuotientGroup.lift q.ker a hka
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ ha hka
  let j : (K ⧸ q.ker) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientKerEquivRange q).trans ((MulEquiv.subgroupCongr hqrange).trans e)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (K ⧸ q.ker) := j.isSimpleGroup
  have hAut : Nat.card (MulAut W) = if d = 4 then 168 else 20160 := hyperplaneAut_card D A C hd
  rcases (inferInstance : g.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff _).mp hk
    have he := Nat.card_congr (Equiv.ofBijective g ⟨hi,hg⟩)
    rw [Nat.card_congr j.toEquiv,nat_card_alternatingGroup,hAut] at he
    split at he <;> norm_num at he
  · have htriv : ∀ b : MulAut W, b = 1 := by
      intro b
      obtain ⟨k,rfl⟩ := hg b
      exact MonoidHom.mem_ker.mp (hk ▸ mem_top k)
    let : Subsingleton (MulAut W) := ⟨fun b c => (htriv b).trans (htriv c).symm⟩
    let : Unique (MulAut W) := ⟨⟨1⟩,htriv⟩
    have he : Nat.card (MulAut W) = 1 := Nat.card_unique
    rw [hAut] at he
    split at he <;> norm_num at he

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Quasisimplicity of the original smaller image forces the containing
image's intrinsic two-core to be central. -/
theorem containing_image_twoCore_central_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G}
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let Kb := ThreeRigidity.image T U K
  have hKb : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have hle : Yb ≤ Kb := map_mono (comap_mono hYK)
  let : IsQuasisimple Yb := residual_image_quasisimple_at h D structural A C B hd
  let : IsQuasisimple (Yb.subgroupOf Kb) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm
  obtain ⟨SK, _, hlocal⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S (residual_image_local_at h D structural A C B hd) hle hKb.subnormal
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hKb.subgroupOf le_rfl
  exact twoCore_le_center_of_quasisimple_local_component htop SK (Yb.subgroupOf Kb) hlocal

/-- Binary linear intrinsic quotients of Y_R feed the existing image exclusion,
without identifying O₂(Y_R) with Y_R ∩ R. -/
theorem residual_eq_containing_of_binary_twoCore_quotient_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) m 2) :
    rigidityHyperplaneResidual L U V = K := by
  apply residual_eq_containing_of_binary_central_cover_at h D structural A C B hd hKN hK hYK
    (QuotientGroup.mk' (pCore 2 (ThreeRigidity.image T U K)))
    (QuotientGroup.mk'_surjective _) _ hm
    (hmodel.of_mulEquiv (containingImageTwoCoreEquiv hKN).symm)
  rw [QuotientGroup.ker_mk']
  exact containing_image_twoCore_central_at h D structural A C B hd hK hYK

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U H P : Subgroup G} {d : ℕ}

omit [Finite G] in
private theorem hyperplane_card_gt_two_at (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : 2 < Nat.card (U ⊓ V : Subgroup G) := by
  rw [C.hyperplane]
  exact lt_of_eq_of_lt (by decide : 2 = 2^1) (pow_lt_pow_right₀ (by decide) (by omega))

/-- Y belongs to the faithful local family under the original ambient hypotheses. -/
theorem residual_mem_faithful_family_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : rigidityHyperplaneResidual L U V ∈ MainForward.faithfulLocalComponents T := by
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (h.simpleQTKE.evenCharacteristic T)).mpr
  refine ⟨residual_mem_local_family D A C hd (((structural L h).2.2 V D).1),?_⟩
  apply ne_bot_of_le_ne_bot _ (hyperplane_le_intrinsic_module D A C hd)
  exact (one_lt_card_iff_ne_bot _).mp (lt_trans (by decide : 1 < 2) (hyperplane_card_gt_two_at C hd))

/-- Any local component containing the original residual is faithful. -/
theorem containing_component_faithful_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K : Subgroup G} (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    K ∈ MainForward.faithfulLocalComponents T :=
  Chapter1.Section02.Adequate.faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T)
    (residual_mem_faithful_family_at h D structural A C hd) hK hYK

/-- The source component chain Y≤Y_R≤Y₀, with relative normality of Y_R
and genuine maximal faithful-family membership of Y₀. -/
theorem source_containing_component_chain_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  obtain ⟨K,hKN,hK,hYK,hn,hlocal⟩ := exists_normal_containing_component_at h D structural A C
    (RigidityKernel.source_centralizers_at h D structural A C hnone) hd
  obtain ⟨K₀,hK₀,hKK₀⟩ := Chapter1.exists_mem_LStar_ge hlocal
  have hf := containing_component_faithful_at h D structural A C hd hK₀.1 (hYK.trans hKK₀)
  exact ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K₀).mp hf).2⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The rank bound before the exceptional A₇ exclusion. -/
theorem source_radical_card_bound_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : Nat.card (sectionRadical T U) ≤ 2 ^ (2*(d-1)+1) := by
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZR : Z ≤ sectionRadical T U := le_sup_right.trans B.centralizer_split.symm.le
  have hn : Z ≤ normalizer (U : Set G) :=
    (hZR.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  rw [show sectionRadical T U = U ⊔ Z from B.centralizer_split,
    card_sup_eq_mul_of_normalizes_of_disjoint U Z hn B.centralizer_disjoint,C.dimension,
    pow_succ]
  exact Nat.mul_le_mul_left _ B.component_centralizer_card

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual normal containing component cannot have the literal exceptional
A₇ image, regardless of whether it equals the original residual. -/
theorem source_containing_component_without_seven_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀⟩ :=
    source_containing_component_chain_at h D structural A C hnone hd
  exact ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,
    no_alternating_seven_containing_image_at h D structural A C
      (RigidityKernel.source_centralizers_at h D structural A C hnone) hd hKN hYK hn⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual elementary radical has binary dimension at most nine. -/
theorem sectionRadical_finrank_le_nine_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    letI : IsElementaryAbelian 2 (sectionRadical T U) :=
      (RigidityKernel.source_centralizers_at h D structural A C hnone).elementary
    Module.finrank (ZMod 2) (Additive (sectionRadical T U)) ≤ 9 := by
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  let : IsElementaryAbelian 2 (sectionRadical T U) := B.elementary
  have hc := source_radical_card_bound_at h D structural A C hnone
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (sectionRadical T U))
  change Nat.card (sectionRadical T U) = _ at he
  rw [Nat.card_zmod] at he
  have hb : 2 * (d-1) + 1 ≤ 9 := by have := A.dimension.2; omega
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive (sectionRadical T U)) ≤ 2^9 :=
    he.symm.trans_le (hc.trans (Nat.pow_le_pow_right (by decide) hb))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- A small maximal-component row forces equality of the actual original
subgroups, using their original common full Sylow. -/
theorem residual_eq_of_containing_solvable_sylow_overgroups_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hYK₀ : rigidityHyperplaneResidual L U V ≤ K₀)
    (hproper : SolvableSylowOvergroups K₀) : rigidityHyperplaneResidual L U V = K₀ := by
  let J := K₀ ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hYJ : rigidityHyperplaneResidual L U V ≤ J := hYK₀.trans le_sup_left
  have hlocal := (Chapter1.mem_LIn_iff_subgroupOf
    (show (T : Subgroup G) ≤ J from le_sup_right) hYJ).mp
    ⟨hYJ,residual_mem_local_family D A C hd (((structural L h).2.2 V D).1)⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups S
    hlocal.1 hK₀.1 (comap_mono hYK₀)
    (SolvableSylowOvergroups.of_equiv (subgroupOfEquivOfLe
      (show K₀ ≤ J from le_sup_left)) hproper)
  have hm := congrArg (Subgroup.map J.subtype) he
  change ((rigidityHyperplaneResidual L U V).subgroupOf J).map J.subtype =
    (K₀.subgroupOf J).map J.subtype at hm
  simpa only [map_subgroupOf_eq_of_le hYJ,
    map_subgroupOf_eq_of_le (show K₀ ≤ J from le_sup_left)] using hm

private theorem small_linear_properSylow_at :
    SolvableSylowOvergroups (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  SolvableSylowOvergroups.of_equiv Matrix.PSL3Two.equiv
    (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simp))

private theorem hexacode_properSylow_at : SolvableSylowOvergroups Atlas.Codes.HexEvenAutomorphisms := by
  let := Representation.Hexacode.even_isPerfect
  exact SolvableSylowOvergroups.of_central_quotient Atlas.Codes.hexEvenCoordinate
    Atlas.Codes.hexEvenCoordinate_surjective Representation.Hexacode.even_kernel_eq_center.le
    AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem small_alternating_properSylow_at {n : ℕ} (hn : n = 5 ∨ n = 6) :
    SolvableSylowOvergroups (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl
  · exact fun _ P _ hP => alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP
  · exact AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem chosen_alternating_properSylow_at {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    {n : ℕ} (hn : n = 5 ∨ n = 6)
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin n)) :
    SolvableSylowOvergroups K₀ := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  have hk : f.ker ≤ center (K₀ ⧸ pCore 2 K₀) := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    have hone (x : alternatingGroup (Fin n)) : x = 1 := by
      obtain ⟨y,rfl⟩ := hf x
      exact DFunLike.congr_fun hz y
    rcases hn with rfl | rfl
    · obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 5))
      exact hx (hone x)
    · obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 6))
      exact hx (hone x)
  exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (SolvableSylowOvergroups.of_central_quotient f hf hk (small_alternating_properSylow_at hn))

/-- Apply original 12.2.2 to the actual proper containing component. The
SL₃, G₂(2)′, triple-six and small alternating rows are discharged here. -/
theorem proper_containing_module_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K₀ W : Subgroup G}
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hYK₀ : rigidityHyperplaneResidual L U V < K₀)
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (rows : ModuleAlternatives1222 E) : ProperContainingModuleRows E := by
  let := E.actionCentralizer_normal
  have hnot : ¬ SolvableSylowOvergroups K₀ := fun hp => hYK₀.ne
    (residual_eq_of_containing_solvable_sylow_overgroups_at h D structural A C hd hK₀ hYK₀.le hp)
  have hsmall {X : Type} [Group X] (e : (K₀ ⧸ pCore 2 K₀) ≃* X)
      (hp : SolvableSylowOvergroups X) : False :=
    hnot (isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (SolvableSylowOvergroups.of_equiv e hp))
  cases rows with
  | linear n hn e =>
    rcases hn with rfl | hn
    · exact (hsmall e.groupEquiv small_linear_properSylow_at).elim
    · exact .linear n hn e
  | linearThreeExtension e _ _ => exact (hsmall e small_linear_properSylow_at).elim
  | linearFiveExterior e hd hi => exact .linearFiveExterior e hd hi
  | alternating n hlo hhi e =>
    have hn : n = 7 ∨ n = 8 := by
      by_contra hh
      exact hnot (chosen_alternating_properSylow_at E hq (by omega) e.groupEquiv)
    exact .alternating n hn e
  | alternatingSevenFour e hd => exact .alternatingSevenFour e hd
  | g2 e => exact (hsmall e.groupEquiv Atlas.G2.binaryDerived_solvableSylowOvergroups).elim
  | tripleSix e _ _ _ => exact (hsmall e hexacode_properSylow_at).elim

/-- In the original source chain a proper normal containing component has
only these larger marked module rows whenever its maximal overcomponent has
quasisimple two-core quotient. No extra classification input is introduced. -/
theorem source_proper_containing_module_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K K₀ : Subgroup G}
    (hYK : rigidityHyperplaneResidual L U V < K) (hKK₀ : K ≤ K₀)
    (hK₀ : FaithfulMaximalLocal T K₀)
    (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)) :
    ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ProperContainingModuleRows E := by
  have h₀ : Hypothesis1223 KnownSimple.IsKnownSimple T K₀ :=
    { h with maximal_faithful := hK₀, quasisimple := hq }
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural K₀ h₀).2.1
  exact ⟨W,E,proper_containing_module_rows_at h D structural A C hd hK₀.1.1
    (lt_of_lt_of_le hYK hKK₀) E hq (modules K₀ W h₀ E)⟩

/-- An exhaustive source reduction: equality closes the full higher rigidity
branch; a proper chain retains only the larger marked 12.2.2 rows or the
nonquasisimple maximal quotient. The final catalogue construction remains here. -/
theorem source_rigidity_or_remaining_containing_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ProperContainingModuleRows E) := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hseven⟩ :=
    source_containing_component_without_seven_at h D structural A C hnone hd
  by_cases he : rigidityHyperplaneResidual L U V = K
  · have hnormal : normalizer (sectionRadical T U : Set G) ≤
        normalizer (rigidityHyperplaneResidual L U V : Set G) := by simpa only [he] using hn
    exact Or.inl ⟨hnormal,source_rigidity_step_of_residual_normal_at h D structural A C hnone hd hnormal⟩
  · have hlt := lt_of_le_of_ne hYK he
    refine Or.inr ⟨K,K₀,hKN,hK,hlt,hn,hlocal,hKK₀,hK₀,
      containing_image_twoCore_central_at h D structural A C
        (RigidityKernel.source_centralizers_at h D structural A C hnone) hd hK hYK,hseven,?_⟩
    by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
    · exact Or.inr (source_proper_containing_module_rows_at h D structural modules A C hd hlt hKK₀ hK₀ hq)
    · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u

private theorem small_binary_central_core_quasisimple_at
    {X : Type u} [Group X] [Finite X] {κ : GroupClass.{u}}
    (hQ : IsSQTK κ (X ⧸ pCore 2 X)) (hX : (⊤ : Subgroup X).IsCComponent)
    (hcentral : pCore 2 X ≤ center X)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) X M) (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) M ≤ 12) : IsQuasisimple X := by
  let Q := pCore 2 X
  let W := BinaryOffender.fixedSpace ρ Q
  have hW := BinaryOffender.fixedSpace_stable_of_normal ρ Q
  let a := BinaryOffender.invariantActionHom ρ W hW
  let : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
  have ha : a.ker = Q := by
    rw [BinaryOffender.invariantActionHom_ker]
    exact BinaryOffender.fixedSpace_kernel_eq_twoCore_of_centralizes ρ hρ ⊤
      (IsPGroup.of_subsingleton 2 _) (by intro x hx y _; exact mem_center_iff.mp (hcentral hx) y)
  let e : (X ⧸ Q) ≃* BinaryOffender.subspaceActionImage ρ W :=
    (QuotientGroup.quotientMulEquivOfEq ha.symm).trans
      (BinaryOffender.invariantActionQuotientEquiv ρ W hW)
  let τ := (BinaryOffender.subspaceImageRepresentation ρ W).comp e.toMonoidHom
  have hτ : Function.Injective τ := (BinaryOffender.subspaceImageRepresentation_injective ρ W).comp e.injective
  let : Group.IsNilpotent Q := pCore_isNilpotent
  have htop : (⊤ : Subgroup (X ⧸ Q)).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hX.map_quotient Q
  have hfit : fittingSubgroup (⊤ : Subgroup (X ⧸ Q)) ≤ center (⊤ : Subgroup (X ⧸ Q)) :=
    ChapterA.Section03.NoncentralFitting.fitting_le_center_of_binary_degree_le_twelve hQ
      (pCore_quotient_pCore_eq_bot 2) htop (τ.comp (⊤ : Subgroup (X ⧸ Q)).subtype)
      (hτ.comp Subtype.val_injective) ((Submodule.finrank_le W).trans hd)
  have hr : solvableRadical (⊤ : Subgroup (X ⧸ Q)) = center (⊤ : Subgroup (X ⧸ Q)) := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm (fun x y => Subtype.ext (mem_center_iff.mp y.property x)))
  let := htop.perfect
  let := htop.isSimpleGroup_quotient_solvableRadical
  let : IsQuasisimple (⊤ : Subgroup (X ⧸ Q)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  let : IsQuasisimple (X ⧸ Q) := IsQuasisimple.of_mulEquiv topEquiv
  let : Group.IsPerfect X := Group.IsPerfect.top_iff.mp hX.perfect
  exact (show PerfectCentralCovering.Cover X (X ⧸ Q) from
    { toMonoidHom := QuotientGroup.mk' Q, surjective := QuotientGroup.mk'_surjective _,
      isPerfect := inferInstance, ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual containing image is quasisimple before its maximal-overcomponent
catalogue is known: its faithful binary degree is at most nine, and its
central two-core can be removed on the fixed space without losing faithfulness. -/
theorem containing_image_quasisimple_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G}
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    IsQuasisimple (ThreeRigidity.image T U K) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let B := RigidityKernel.source_centralizers_at h D structural A C hnone
  let : IsElementaryAbelian 2 R := B.elementary
  have hRtwo : IsPGroup 2 R := IsElementaryAbelian.isPGroup 2 R
  have hRne : R ≠ ⊥ := ne_bot_of_le_ne_bot (C.core_ne_bot (by omega : 2 ≤ d))
    (le_inf C.core_le_sylow (by let := C.elementary; exact le_centralizer U))
  have hN : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk ⟨R,hRne,hRtwo,rfl⟩
  have hNR : IsSQTK KnownSimple.IsKnownSimple (NormalizerQuotient R) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (R.subgroupOf N) hRtwo.comap_subtype).trans
      (hN.stronglyQuasithin p hp ho)
  let Kb := ThreeRigidity.image T U K
  have hKb := hNR.subgroup Kb
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Kb ⧸ pCore 2 Kb) := by
    refine ⟨?_,hKb.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hKb.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (R.subgroupOf N) := hRtwo.comap_subtype.isNilpotent
  have hcomp : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hcomp.subgroupOf le_rfl
  have he := sectionRadical_selfCentralizing h A C B
  let a := (action R he.symm.le).comp Kb.subtype
  have ha : Function.Injective a := (action_injective R he).comp Kb.subtype_injective
  let σ := Representation.elementaryRepresentation (p := 2) a
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply ha
    apply MulEquiv.ext
    intro r
    exact congrArg Additive.toMul (congrArg
      (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul r)) hxy)
  apply small_binary_central_core_quasisimple_at hQ htop
    (containing_image_twoCore_central_at h D structural A C B hd hK hYK) σ hσ
  have hh := sectionRadical_finrank_le_nine_at h D structural A C hnone
  change Module.finrank (ZMod 2) (Additive R) ≤ 9 at hh
  omega

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual larger binary quotient gives a binary intrinsic quotient
of the normal containing component, and hence equality with the residual. -/
theorem residual_eq_of_containing_binary_maximal_quotient_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    {n : ℕ} (hn : n ≤ 5)
    (e : (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup n) :
    rigidityHyperplaneResidual L U V = K := by
  obtain ⟨m,hm,hmn,⟨a⟩⟩ :=
    ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient_of_containing_quotient
      T hlocal.1 hK₀.1 hKK₀ n hn e
  exact residual_eq_containing_of_binary_twoCore_quotient_at h D structural A C B hd hKN hK hYK
    (by omega : m = 3 ∨ m = 4 ∨ m = 5)
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
      ⟨a.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m)).symm⟩⟩

private def chosen_alternating_eight_linear_quotient_at {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 8)) :
    (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup 4 := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  let a := MulEquiv.ofBijective f ⟨AlternatingEight.reduced_cover_injective f hf
    (pCore_quotient_pCore_eq_bot 2),hf⟩
  exact a.trans (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)))

/-- Eliminate the larger linear, exterior and A8 rows at the actual
containing component. The remaining A7 rows keep their module marking. -/
theorem exceptional_containing_module_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (rows : ProperContainingModuleRows E) : ExceptionalContainingModuleRows E := by
  let := E.actionCentralizer_normal
  have hnot {n : ℕ} (hn : n ≤ 5)
      (e : (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup n) : False :=
    hYK.ne (residual_eq_of_containing_binary_maximal_quotient_at h D structural A C B hd
      hKN hK hYK.le hlocal hKK₀ hK₀ hn e)
  cases rows with
  | linear n hn e =>
    exact (hnot (by omega) (e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n))).elim
  | linearFiveExterior e _ _ =>
    exact (hnot (by decide) (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5))).elim
  | alternating n hn e =>
    rcases hn with rfl | rfl
    · exact .alternatingSeven e
    · exact (hnot (by decide) (chosen_alternating_eight_linear_quotient_at E hq e.groupEquiv)).elim
  | alternatingSevenFour e hd => exact .alternatingSevenFour e hd

/-- The exhaustive source reduction after the binary Levi catalogue:
full rigidity, or the original proper chain with a nonquasisimple maximal
head or one of the two marked A7 rows. Final assembly retains those cases. -/
theorem source_rigidity_or_exceptional_containing_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ExceptionalContainingModuleRows E) := by
  rcases source_rigidity_or_remaining_containing_rows_at h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,hrows⟩ := hc
    refine Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,?_⟩
    rcases hrows with hnot | ⟨W,E,hrows⟩
    · exact Or.inl hnot
    · by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
      · exact Or.inr ⟨W,E,exceptional_containing_module_rows_at h D structural A C
          (RigidityKernel.source_centralizers_at h D structural A C hnone) hd
          hKN hK hYK hlocal hKK₀ hK₀.1.1 E hq hrows⟩
      · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

theorem residual_seven_image_card_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d)
    (f : rigidityHyperplaneResidual L U V →* alternatingGroup (Fin 7))
    [Group.IsSolvable f.ker] : d = 4 ∧ Nat.card f.range = 168 := by
  let Y := rigidityHyperplaneResidual L U V
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural L h).2.2 V D).1))
  let := (hyperplaneAut_simple_perfect C hd).1
  let : IsSimpleGroup (Y ⧸ pCore 2 Y) := (residualQuotientAutEquiv D A C hd).isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    apply pCore_isPGroup.to_le
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  let e := f.rangeRestrict.pCoreQuotientEquiv (p := 2) f.rangeRestrict_surjective (by
    show IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hk)
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = if d = 4 then 168 else 20160 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr (residualQuotientAutEquiv D A C hd).toEquiv]
    exact hyperplaneAut_card D A C hd
  obtain ⟨k,hkcard⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hdiv : (if d = 4 then 168 else 20160) * 2^k ∣ 2520 := by
    have hh := f.range.card_subgroup_dvd_card
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range),hc,hkcard] at hh
    simpa only [nat_card_alternatingGroup,Nat.card_fin,show Nat.factorial 7 / 2 = 2520 from by decide] using hh
  have hd4 : d = 4 := by
    by_contra hh
    rw [if_neg hh] at hdiv
    have hh := (dvd_mul_right 20160 (2^k)).trans hdiv
    norm_num at hh
  rw [if_pos hd4] at hc hdiv
  have hpow : 2^k ∣ 15 := by
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 168)).mp hdiv
  have hone : 2^k = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 15).pow_left k) (dvd_refl _) hpow
  refine ⟨hd4,?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range),hc,hkcard,hone,mul_one]

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
open ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

private theorem chosen_seven_core_kernel_central_at {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    letI := E.actionCentralizer_normal
    (e.toMonoidHom.comp E.coreToFaithful).ker ≤ center (K₀ ⧸ pCore 2 K₀) := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
  intro ht
  have hz : f = 1 := f.ker_eq_top_iff.mp ht
  have hone (x : alternatingGroup (Fin 7)) : x = 1 := by
    obtain ⟨y,rfl⟩ := hf x
    exact DFunLike.congr_fun hz y
  obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
  exact hx (hone x)

private theorem restriction_range_at {X Q : Type*} [Group X] [Group Q]
    {B K : Subgroup X} (hBK : B ≤ K) (f : K →* Q) :
    (f.comp (inclusion hBK)).range = (B.subgroupOf K).map f := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨inclusion hBK b,b.property,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩

/-- A proper containing component in either marked A7 row surjects onto
that exact A7 quotient. The residual has its actual order-168 image. -/
theorem proper_containing_seven_projection_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K K₀ W : Subgroup G}
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    d = 4 ∧
      Nat.card (((rigidityHyperplaneResidual L U V).subgroupOf K₀).map
        (chosenSevenProjection E e)) = 168 ∧
      Function.Surjective ((chosenSevenProjection E e).comp (inclusion hKK₀)) := by
  let := E.actionCentralizer_normal
  let Y := rigidityHyperplaneResidual L U V
  let F := chosenSevenProjection E e
  have hYK₀ : Y ≤ K₀ := hYK.le.trans hKK₀
  let f := F.comp (inclusion hYK₀)
  let : Group.IsSolvable F.ker := chosenSevenProjection_kernel_solvable E hq e
  let j : f.ker →* F.ker :=
    { toFun := fun x => ⟨inclusion hYK₀ x.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun x y hh => Subtype.ext (Subtype.ext
      (congrArg (fun z : F.ker => (z.val : G)) hh)))
  obtain ⟨hd4,hcard⟩ := residual_seven_image_card_at h D structural A C hd f
  have hycard : Nat.card ((Y.subgroupOf K₀).map F) = 168 := by
    rwa [restriction_range_at hYK₀ F] at hcard
  have heq_or := AlternatingSeven.Containing.eq_or_top_of_card
    ((Y.subgroupOf K₀).map F) ((K.subgroupOf K₀).map F) hycard (map_mono (comap_mono hYK.le))
  refine ⟨hd4,hycard,?_⟩
  rcases heq_or with heq | htop
  · obtain ⟨S,hS,hKS⟩ := BinaryIntrinsic.local_in_local_overgroup T hlocal.1 hK₀.1 hKK₀
    have hYS : Y.subgroupOf K₀ ∈ ChapterA.Section03.localCComponents S := by
      rw [hS]
      exact local_restrict (residual_mem_local_family D A C hd
        (((structural L h).2.2 V D).1)).1 hYK₀
    have hh : Y.subgroupOf K₀ = K.subgroupOf K₀ :=
      local_eq_of_central_twoCore_map_eq S hYS hKS (comap_mono hYK.le)
        (e.toMonoidHom.comp E.coreToFaithful) (chosen_seven_core_kernel_central_at E hq e) heq.symm
    have hm := congrArg (map K₀.subtype) hh
    rw [map_subgroupOf_eq_of_le hYK₀,map_subgroupOf_eq_of_le hKK₀] at hm
    exact (hYK.ne hm).elim
  · apply MonoidHom.range_eq_top.mp
    rw [restriction_range_at hKK₀ F]
    exact htop

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The original exhaustive source reduction now retains a surjection from the
actual proper containing component to the marked seven-point quotient, and
identifies the smaller image there. The nonquasisimple head and the central
cover of this projection remain to be discharged by the final rigidity owner. -/
theorem source_rigidity_or_marked_seven_projection_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ hKK₀ : K ≤ K₀, FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        (IsQuasisimple (K₀ ⧸ pCore 2 K₀) ∧
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ExceptionalContainingModuleRows E ∧
        letI := E.actionCentralizer_normal
        ∃ e : (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7),
          d = 4 ∧
          Nat.card (((rigidityHyperplaneResidual L U V).subgroupOf K₀).map
            (chosenSevenProjection E e)) = 168 ∧
          Function.Surjective ((chosenSevenProjection E e).comp (inclusion hKK₀)))) := by
  rcases source_rigidity_or_exceptional_containing_rows_at h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,hrows⟩ := hc
    refine Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,?_⟩
    rcases hrows with hnot | ⟨W,E,hrows⟩
    · exact Or.inl hnot
    · by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
      · refine Or.inr ⟨hq,W,E,hrows,?_⟩
        let := E.actionCentralizer_normal
        have he : Nonempty ((K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃*
            alternatingGroup (Fin 7)) := by
          cases hrows with
          | alternatingSeven e => exact ⟨e.groupEquiv⟩
          | alternatingSevenFour e _ => exact ⟨e⟩
        obtain ⟨e⟩ := he
        exact ⟨e,proper_containing_seven_projection_at h D structural A C hd hYK hlocal hKK₀
          hK₀.1.1 E hq e⟩
      · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The chosen-module action centralizes the containing A₇ image pointwise. -/
theorem chosen_centralizes_seven_central_cover_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168)
    (v : V) :
    quotient (sectionRadical T U) ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩ ∈
      centralizer (ThreeRigidity.image T U K : Set (NormalizerQuotient (sectionRadical T U))) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let Kb := ThreeRigidity.image T U K
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let vN : N := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  let : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Kb.Normal := Subgroup.Normal.map inferInstance (quotient R) (QuotientGroup.mk'_surjective _)
  let := residual_image_quasisimple_at h D structural A C B hd
  let YK := Yb.subgroupOf Kb
  let : IsQuasisimple YK := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show Yb ≤ Kb from map_mono (comap_mono hYK))).symm
  change Nat.card (YK.map f.toMonoidHom) = 168 at hcard
  let : Group.IsPerfect (YK.map f.toMonoidHom) := Group.IsPerfect.map _
  let : Nontrivial (YK.map f.toMonoidHom) := by
    apply (nontrivial_iff_ne_bot _).mpr
    intro he
    have hh : Nat.card (YK.map f.toMonoidHom) = 1 := by rw [he]; simp
    omega
  apply AlternatingSeven.SevenFixer.central_cover_centralizes_of_centralizes_subgroup Kb Yb
    (map_mono (comap_mono hYK)) f (Group.IsPerfect.not_isSolvable _)
    (by rw [hcard]; decide)
    (quotient R vN) (by exact (normalizer_eq_top Kb).symm ▸ mem_top _)
  rintro yb ⟨y,hy,rfl⟩
  have hc := chosen_residual_actions_commute D A C B v ⟨y,hy⟩
  apply (action_injective R (sectionRadical_selfCentralizing h A C B))
  rw [map_mul,map_mul]
  change R.normalizerMonoidHom y * R.normalizerMonoidHom vN =
    R.normalizerMonoidHom vN * R.normalizerMonoidHom y
  exact hc.eq.symm

/-- The original displacement space is invariant under the containing image,
using the actual commutator map, not its dimension or an abstract module tag. -/
theorem containing_normalizes_hyperplane_of_seven_cover_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168) :
    K ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let := D.elementary
  obtain ⟨v,δ,hv,hδ,hδval,_,_⟩ := exists_radical_displacement D A C B
    (((structural L h).2.2 V D).1)
  let vN : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  have hvc := chosen_centralizes_seven_central_cover_at h D structural A C B hd hYK hn f hcard v
  apply le_normalizer_iff.mpr
  intro k hk w hw
  obtain ⟨r,hr⟩ := hδ ⟨w,hw⟩
  let kN : normalizer (R : Set G) := ⟨k,hKN hk⟩
  have hc : Commute (R.normalizerMonoidHom vN) (R.normalizerMonoidHom kN) := by
    have hh := congrArg (action R (by exact (sectionRadical_selfCentralizing h A C B).symm.le))
      (hvc (quotient R kN) (mem_map_of_mem (quotient R) hk))
    rw [map_mul,map_mul] at hh
    change R.normalizerMonoidHom kN * R.normalizerMonoidHom vN =
      R.normalizerMonoidHom vN * R.normalizerMonoidHom kN at hh
    exact hh.symm
  have he := congrArg (fun r : R => (r : G)) (ConjugationDisplacement.equivariant R vN kN hc r)
  have he' : (δ (R.normalizerMonoidHom kN r) : G) = k * w * k⁻¹ := by
    rw [hδval]
    rw [← ConjugationDisplacement.hom_apply R vN (R.normalizerMonoidHom kN r)]
    rw [he]
    change k * (ConjugationDisplacement.hom R vN r : G) * k⁻¹ = _
    rw [ConjugationDisplacement.hom_apply,← hδval r,hr]
  exact he' ▸ (δ (R.normalizerMonoidHom kN r)).property

/-- Even a central cover of the marked A₇ quotient is incompatible with the
literal hyperplane displacement action. -/
theorem no_seven_central_cover_containing_image_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)))
    (hcard : Nat.card (((ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)).subgroupOf
      (ThreeRigidity.image T U K)).map f.toMonoidHom) = 168) : False := by
  let R := sectionRadical T U
  let W := U ⊓ V
  let Kb := ThreeRigidity.image T U K
  have hKW := containing_normalizes_hyperplane_of_seven_cover_at h D structural A C B hd hKN hYK hn f hcard
  let a : K →* MulAut W := W.normalizerMonoidHom.comp (inclusion hKW)
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨y,hy⟩ := residualHyperplaneAction_surjective D A C hd b
    exact ⟨⟨y,hYK y.property⟩,hy⟩
  let q := containingImageMap hKN
  have hq := containingImageMap_surjective hKN
  have hka : q.ker ≤ a.ker := by
    intro k hk
    have hkR : (k : G) ∈ R :=
      (QuotientGroup.eq_one_iff (⟨k,hKN k.property⟩ : normalizer (R : Set G))).mp
        (congrArg Subtype.val hk)
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hkR.2 w w.property.1).symm
  let g : Kb →* MulAut W := q.liftOfSurjective hq ⟨a,hka⟩
  have hgq (k : K) : g (q k) = a k := by simp [g]
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨k,rfl⟩ := ha b
    exact ⟨q k,hgq k⟩
  let := (hyperplaneAut_simple_perfect C hd).1
  let := (hyperplaneAut_simple_perfect C hd).2
  have hz : center (MulAut W) = ⊥ := by
    rcases (inferInstance : (center (MulAut W)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  have hfg : f.toMonoidHom.ker ≤ g.ker := by
    intro x hx
    have hc : g x ∈ center (MulAut W) := mem_center_iff.mpr (fun y => by
      obtain ⟨y,rfl⟩ := hg y
      exact (map_mul g y x).symm.trans
        ((congrArg g (mem_center_iff.mp (f.ker_le_center hx) y)).trans (map_mul g x y)))
    change g x = 1
    exact mem_bot.mp (hz ▸ hc)
  let b : alternatingGroup (Fin 7) →* MulAut W :=
    f.toMonoidHom.liftOfSurjective f.surjective ⟨g,hfg⟩
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x,rfl⟩ := hg y
    exact ⟨f.toMonoidHom x,by simp [b]⟩
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hAut : Nat.card (MulAut W) = if d = 4 then 168 else 20160 := hyperplaneAut_card D A C hd
  rcases (inferInstance : b.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff _).mp hk
    have he := Nat.card_congr (Equiv.ofBijective b ⟨hi,hb⟩)
    rw [nat_card_alternatingGroup,hAut] at he
    split at he <;> norm_num at he
  · have htriv : ∀ y : MulAut W, y = 1 := by
      intro y
      obtain ⟨x,rfl⟩ := hb y
      exact MonoidHom.mem_ker.mp (hk ▸ mem_top x)
    let : Unique (MulAut W) := ⟨⟨1⟩,htriv⟩
    have he : Nat.card (MulAut W) = 1 := Nat.card_unique
    rw [hAut] at he
    split at he <;> norm_num at he

/-- Transport the actual seven-point projection to KR/R, including its
representative equation and central kernel. -/
theorem exists_seven_image_cover_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K W) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : letI := E.actionCentralizer_normal
      (K ⧸ (centralizer (W : Set G)).subgroupOf K) ≃* alternatingGroup (Fin 7)) :
    ∃ f : PerfectCentralCovering.Cover (ThreeRigidity.image T U K) (alternatingGroup (Fin 7)),
      ∀ k : K, f.toMonoidHom (containingImageMap hKN k) = chosenSevenProjection E e k := by
  let := E.actionCentralizer_normal
  let := Chapter1.mem_L_isPerfect hlocal
  let F := chosenSevenProjection E e
  have hF : Function.Surjective F := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective hF
  let q := containingImageMap hKN
  have hqs := containingImageMap_surjective hKN
  let J := q.ker.map F
  let : J.Normal := (inferInstance : q.ker.Normal).map F hF
  have hJ : IsPGroup 2 J := (containingImageMap_ker_isPGroup hKN).map F
  have hJb : J = ⊥ := by
    apply (inferInstance : J.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let : Group.IsNilpotent J := hJ.isNilpotent
    let a : J ≃* alternatingGroup (Fin 7) := (MulEquiv.subgroupCongr ht).trans topEquiv
    exact Group.IsPerfect.not_isSolvable _
      (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)
  have hk : q.ker ≤ F.ker := (map_eq_bot_iff q.ker).mp hJb
  let f : ThreeRigidity.image T U K →* alternatingGroup (Fin 7) :=
    q.liftOfSurjective hqs ⟨F,hk⟩
  have he (k : K) : f (q k) = F k := by simp [f]
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k,rfl⟩ := hF x
    exact ⟨q k,he k⟩
  let Kb := ThreeRigidity.image T U K
  let : Group.IsPerfect Kb := Group.IsPerfect.ofSurjective hqs
  let : IsQuasisimple (Kb ⧸ pCore 2 Kb) :=
    IsQuasisimple.of_mulEquiv (containingImageTwoCoreEquiv hKN)
  let : IsQuasisimple Kb :=
    (show PerfectCentralCovering.Cover Kb (Kb ⧸ pCore 2 Kb) from
      { toMonoidHom := QuotientGroup.mk' _, surjective := QuotientGroup.mk'_surjective _,
        isPerfect := inferInstance, ker_le_center := by
          rw [QuotientGroup.ker_mk']
          exact containing_image_twoCore_central_at h D structural A C B hd hK hYK }).isQuasisimple
  have hfc : f.ker ≤ center Kb := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨k,rfl⟩ := hf x
    exact hx (DFunLike.congr_fun hz k)
  exact ⟨{ toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hfc },he⟩

/-- Both marked A₇ rows of the actual maximal overcomponent are impossible.
The original projection descends to KR/R and the hyperplane displacement
exclusion applies with its order-168 embedded residual image. -/
theorem no_proper_containing_seven_projection_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨_,hcard,hs⟩ := proper_containing_seven_projection_at h D structural A C hd hYK
    hlocal hKK₀ hK₀ E hq e
  have heq := containing_eq_maximal_of_seven_projection hlocal hKK₀ hK₀ E hq e hs
  subst K₀
  obtain ⟨f,hf⟩ := exists_seven_image_cover_at h D structural A C B hd hKN hK hYK.le hlocal E hq e
  apply no_seven_central_cover_containing_image_at h D structural A C B hd hKN hYK.le hn f
  rw [← containingImageMap_subgroup_map hKN hYK.le,map_map]
  have he : f.toMonoidHom.comp (containingImageMap hKN) = chosenSevenProjection E e :=
    MonoidHom.ext hf
  rw [he]
  exact hcard

/-- All quasisimple maximal-containing rows of original 12.2.2 now close
rigidity and the actual parabolic splitting. Only the nonquasisimple maximal
two-core quotient remains in the exhaustive source reduction. -/
theorem source_rigidity_or_nonquasisimple_maximal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀) := by
  rcases source_rigidity_or_marked_seven_projection_at h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,_,hrows⟩ := hc
    rcases hrows with hnot | ⟨hq,W,E,_,e,_,_,_⟩
    · exact Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hnot⟩
    · exact (no_proper_containing_seven_projection_at h D structural A C
        (RigidityKernel.source_centralizers_at h D structural A C hnone) hd hKN hK hYK hn
        hlocal hKK₀ hK₀.1.1 E hq e).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end

section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Every solvable-kernel image of the original residual retains its seven part. -/
theorem seven_dvd_residual_image_of_solvable_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {Q : Type*} [Group Q]
    (f : rigidityHyperplaneResidual L U V →* Q) [Group.IsSolvable f.ker] :
    7 ∣ Nat.card f.range := by
  let Y := rigidityHyperplaneResidual L U V
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural L h).2.2 V D).1))
  let := (hyperplaneAut_simple_perfect C hd).1
  let : IsSimpleGroup (Y ⧸ pCore 2 Y) := (residualQuotientAutEquiv D A C hd).isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    apply pCore_isPGroup.to_le
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  let e := f.rangeRestrict.pCoreQuotientEquiv (p := 2) f.rangeRestrict_surjective (by
    show IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hk)
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = if d = 4 then 168 else 20160 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr (residualQuotientAutEquiv D A C hd).toEquiv]
    exact hyperplaneAut_card D A C hd
  have hdv : 7 ∣ Nat.card (f.range ⧸ pCore 2 f.range) := by
    rw [hc]
    split <;> decide
  exact hdv.trans (card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))

/-- A prime-field PSL₂ central cover cannot properly enlarge this residual:
the only proper nonsolvable local image is A₅, which has no seven part. -/
theorem residual_eq_containing_of_prime_linear_central_cover_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {Q : Type*} [Group Q] [Finite Q]
    (f : ThreeRigidity.image T U K →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (ThreeRigidity.image T U K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmodel : ClassicalGroup.IsPSL Q 2 p) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (R.subgroupOf N) :=
    ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let Kb := ThreeRigidity.image T U K
  have hKb : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have hle : Yb ≤ Kb := map_mono (comap_mono hYK)
  obtain ⟨SK,_,hlocal⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S (residual_image_local_at h D structural A C B hd) hle hKb.subnormal
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
    Subtype.ext (mem_center_iff.mp (hk y.property) x.val))
  have hJ := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hKb.subgroupOf le_rfl
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective f hf] using cComponent_map_of_solvable_ker htop f hf
  let j := f.comp (inclusion hle)
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hle).subgroupComap f.ker)
    (fun x y he => Subtype.ext ((inclusion_injective hle) (congrArg Subtype.val he)))
  let q := containingImageMap B.residual_normalizes
  let : Group.IsNilpotent q.ker := (containingImageMap_ker_isPGroup B.residual_normalizes).isNilpotent
  let : Group.IsSolvable (j.comp q).ker := isSolvable_comap_of_solvable_ker q j.ker
  have hseven : 7 ∣ Nat.card ((Yb.subgroupOf Kb).map f) := by
    have hh := seven_dvd_residual_image_of_solvable_kernel_at h D structural A C hd (j.comp q)
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (containingImageMap_surjective B.residual_normalizes),← MonoidHom.range_eq_map,
      MonoidHom.range_comp,inclusion_range] at hh
    exact hh
  have heq : (Yb.subgroupOf Kb).map f = ⊤ := by
    by_contra hne
    obtain ⟨_,⟨e⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
      (SK.mapSurjective hf) hJ hQ le_top hne hp ho (hmodel.of_mulEquiv topEquiv)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hseven
    norm_num at hseven
  let := hKb.perfect
  have ht : Yb.subgroupOf Kb = ⊤ := top_unique
    (perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup Kb) (Yb.subgroupOf Kb)
      (by rw [heq]; exact le_top))
  exact residual_eq_containing_of_image_eq_at h D structural A C B hd hKN hK hYK
    (le_antisymm hle (subgroupOf_eq_top.mp ht))

/-- The original prime-field projection descends through the literal image
map, and quasisimplicity makes its remaining kernel central. -/
theorem residual_eq_containing_of_prime_linear_projection_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (F : K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hF : Function.Surjective F) :
    rigidityHyperplaneResidual L U V = K := by
  let : Fact p.Prime := ⟨hp⟩
  let Q := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)
  let r := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let f₀ := r.comp F
  have hf₀ : Function.Surjective f₀ :=
    (GorensteinWalter.sl2ProjectiveProjection_surjective (ZMod p)).comp hF
  let : IsSimpleGroup Q := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  let : Group.IsPerfect Q := GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp3)
  let q := containingImageMap hKN
  have hqs := containingImageMap_surjective hKN
  let J := q.ker.map f₀
  let : J.Normal := (inferInstance : q.ker.Normal).map f₀ hf₀
  have hJ : IsPGroup 2 J := (containingImageMap_ker_isPGroup hKN).map f₀
  have hJb : J = ⊥ := by
    apply (inferInstance : J.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    have hpQ : IsPGroup 2 Q := hJ.of_equiv ((MulEquiv.subgroupCongr ht).trans topEquiv)
    exact Group.IsPerfect.not_isNilpotent Q hpQ.isNilpotent
  have hk : q.ker ≤ f₀.ker := (map_eq_bot_iff q.ker).mp hJb
  let f : ThreeRigidity.image T U K →* Q := q.liftOfSurjective hqs ⟨f₀,hk⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨k,rfl⟩ := hf₀ x
    exact ⟨q k,by simp [f]⟩
  let : IsQuasisimple (ThreeRigidity.image T U K) :=
    containing_image_quasisimple_at h D structural A C hnone hd hK hYK
  have hfc : f.ker ≤ center (ThreeRigidity.image T U K) := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    have hz : f = 1 := f.ker_eq_top_iff.mp ht
    obtain ⟨x,hx⟩ := exists_ne (1 : Q)
    obtain ⟨k,rfl⟩ := hf x
    exact hx (DFunLike.congr_fun hz k)
  exact residual_eq_containing_of_prime_linear_central_cover_at h D structural A C
    (RigidityKernel.source_centralizers_at h D structural A C hnone) hd hKN hK hYK f hf hfc
    hp (hp.odd_of_ne_two (by omega))
    ⟨ZMod p,inferInstance,inferInstance,Nat.card_zmod p,⟨MulEquiv.refl _⟩⟩

/-- The last nonquasisimple maximal row also forces equality of the actual
residual and its containing component. -/
theorem residual_eq_of_nonquasisimple_maximal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K K₀ : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) : rigidityHyperplaneResidual L U V = K := by
  obtain ⟨p,hp,hp3,F,hF,_⟩ := nonquasisimple_containing_prime_projection h hlocal hKK₀ hK₀ hn
  exact residual_eq_containing_of_prime_linear_projection_at h D structural A C hnone hd
    hKN hK hYK hp hp3 F hF

/-- Residual normality in the original ambient normalizer, with every
containing-component alternative discharged. -/
theorem source_residual_normal_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) := by
  rcases source_rigidity_or_nonquasisimple_maximal_at h D structural modules A C hnone hd with hc | hc
  · exact hc.1
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,_,hnot⟩ := hc
    have he := residual_eq_of_nonquasisimple_maximal_at h D structural A C hnone hd
      hKN hK hYK.le hlocal hKK₀ hK₀.1.1 hnot
    simpa only [he] using hn

/-- The higher-dimensional source rigidity and actual parabolic complement,
with no remaining normality or model-recognition premise. -/
theorem source_higher_rigidity_step_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U :=
  source_rigidity_step_of_residual_normal_at h D structural A C hnone hd
    (source_residual_normal_at h D structural modules A C hnone hd)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
end
