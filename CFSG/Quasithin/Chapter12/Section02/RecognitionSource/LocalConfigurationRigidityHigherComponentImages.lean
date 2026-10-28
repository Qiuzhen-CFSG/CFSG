module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSections
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The quasisimple residual image in the literal radical quotient

Write Y=O²(N_L(U∩V)) and R=C_T(U), with d>3. The kernel of Y's full
hyperplane action is O₂(Y). Its normality in YT puts it inside T; the
proved hyperplane centralizer calculation then puts it in RV. Since
[V,Y]≤U∩V≤R, that kernel is central modulo R. Conversely Y∩R fixes
the hyperplane. Thus the actual image YR/R is a perfect central cover
of Aut(U∩V), and is quasisimple. The original full Sylow also supplies
its literal local C-component condition after this quotient.

This establishes the smaller-image premise used by HigherComponentExclusions.
It does not yet identify the image with the centerless binary linear group,
classify its containing image, or assert residual normality.

Source: Aschbacher–Smith, original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The hyperplane-action kernel lies in the original radical times V. -/
theorem residual_core_le_radical_sup_chosen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    (rigidityHyperplaneResidual L U V).pCoreIn 2 ≤ sectionRadical T U ⊔ V := by
  let Y := rigidityHyperplaneResidual L U V
  let J := Y ⊔ (T : Subgroup G)
  have hTY := sylow_normalizes_residual D C (((structural G T L h).2.2 V D).1)
  have hcoreT : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes (show Y ≤ J from le_sup_left)
      (sup_le Y.le_normalizer hTY)).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hc := le_inf hcoreT (residual_core_centralizes_hyperplane D A C hd)
  rw [RigidityKernel.hyperplane_centralizer_eq_core_sup_kernel h D structural A C,
    B.kernel_split] at hc
  exact hc.trans (sup_le (le_sup_left.trans B.centralizer_split.symm.le |>.trans le_sup_left)
    (sup_le le_sup_right (le_sup_right.trans B.centralizer_split.symm.le |>.trans le_sup_left)))

/-- Modulo R the hyperplane-action kernel is central in the residual image. -/
theorem residual_core_commutator_le_radical
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  have hxRV := residual_core_le_radical_sup_chosen h D structural A C B hd hx
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
theorem residual_image_quasisimple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    exact residual_core_commutator_le_radical h D structural A C B hd
      (commutator_mem_commutator (mem_map_of_mem Y.subtype hy) z.property)
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural G T L h).2.2 V D).1))
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
theorem residual_image_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
        (((structural G T L h).2.2 V D).1)⟩
  let : Group.IsSolvable (quotient R).ker := by
    change Group.IsSolvable (QuotientGroup.mk' (R.subgroupOf N)).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal.1 (quotient R)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
