module
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCore
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF

/-!
# Source center-freeness in the original tensor branch

The tensor coordinates identify the original faithful action with a subgroup
of the determinant tensor's full linear normalizer. Its non-FF property
therefore holds for every intermediate actor normalizing L₀ and V. In
particular J(T) centralizes V: otherwise the original Thompson-action theorem
would produce an FF offender.

The source standing guard supplies H in H*(T,M). The proved noncentral
omega-center branch of 3.1.8 would force Thompson movement, so Ω₁Z(T)
centralizes H. The central branch of 3.1.7 then gives Z(L₀T)=1. This
discharges the center input in the Omega-core cohomology and interval results;
the larger-Omega commutator bound remains with its numerical source proof.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
3.1.7–8, 3.2.10(9), and 9.2.2, printed pp.575–576, 583, and730.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original faithful action is non-FF for every intermediate actor
normalizing both the marked orbit actor and the full module. -/
theorem fullModule_actionImage_notFF
    (H : Subgroup G) (hLH : localOrbit T L ≤ H)
    (hHL : H ≤ normalizer (localOrbit T L : Set G))
    (hHV : H ≤ normalizer (D.fullModule : Set G)) :
    let := m.fullModule_elementary
    ¬ BinaryOffender.IsFFModule (ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV) := by
  classical
  let := m.fullModule_elementary
  let ρ := ChapterD.UniqueFactor.imageRepresentation H D.fullModule hHV
  let a := (ChapterD.UniqueFactor.actionHom H D.fullModule hHV).rangeRestrict
  let i : localOrbit T L →* H := inclusion hLH
  let j : localOrbit T L →* ChapterD.internalActionImage H D.fullModule hHV := a.comp i
  have hnormal : i.range.Normal := by
    have hi : i.range = (localOrbit T L).subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi]
    exact normal_subgroupOf_of_le_normalizer hHL
  let : i.range.Normal := hnormal
  have hjnormal : j.range.Normal := by
    rw [show j.range = i.range.map a from MonoidHom.range_comp _ _]
    exact Subgroup.Normal.map inferInstance a (MonoidHom.rangeRestrict_surjective _)
  let : j.range.Normal := hjnormal
  let c : D.fullModule ≃* Multiplicative Binary.V :=
    MulEquiv.ofBijective m.sectionData.coordinates ⟨m.coordinates_injective,m.sectionData.onto⟩
  let E : Additive D.fullModule ≃ₗ[ZMod 2] Binary.V :=
    { toFun := fun v => (c v.toMul).toAdd
      invFun := fun w => Additive.ofMul (c.symm (Multiplicative.ofAdd w))
      left_inv := fun _ => congrArg Additive.ofMul (c.symm_apply_apply _)
      right_inv := fun _ => congrArg Multiplicative.toAdd (c.apply_symm_apply _)
      map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _)
      map_smul' := ZMod.map_smul
        ({ toFun := fun v : Additive D.fullModule => (c v.toMul).toAdd
           map_zero' := congrArg Multiplicative.toAdd c.map_one
           map_add' := fun _ _ => congrArg Multiplicative.toAdd (c.map_mul _ _) } :
            Additive D.fullModule →+ Binary.V) }
  let b : Representation.Equiv (ρ.comp j) (Binary.action.comp m.quotient) :=
    { __ := E
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        exact m.sectionData.equivariant h v.toMul }
  exact Binary.not_ff_of_marked_normal_range ρ
    (ChapterD.UniqueFactor.imageRepresentation_injective H D.fullModule hHV)
    j m.quotient m.onto b

/-- Tensor non-FF forces the actual Thompson subgroup of T to centralize V. -/
theorem thompson_centralizes_fullModule :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.fullModule : Set G) := by
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    by_contra hn
    have hff := D.module_isFF_of_thompson_not_centralizes hn
    have hnon := m.fullModule_actionImage_notFF (localJoin T L) le_sup_left
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
      (by rw [← m.module_eq]; exact D.join_normalizes_module)
    have ht (U V : Subgroup G) (he : U = V)
        (hnU : localJoin T L ≤ normalizer (U : Set G))
        (hnV : localJoin T L ≤ normalizer (V : Set G))
        (hU : IsElementaryAbelian 2 U) (hV : IsElementaryAbelian 2 V) :
        @BinaryOffender.IsFFModule _ _ _ _ _
          (@ChapterD.UniqueFactor.imageRepresentation _ _ (localJoin T L) U hnU hU) →
        @BinaryOffender.IsFFModule _ _ _ _ _
          (@ChapterD.UniqueFactor.imageRepresentation _ _ (localJoin T L) V hnV hV) := by
      subst V
      exact id
    exact hnon (ht _ _ m.module_eq _ _ D.module_elementary m.fullModule_elementary hff)
  rwa [m.module_eq] at hJ

/-- The genuine outside-maximal guard discharges source 3.1.8(3) for L₀T. -/
theorem localJoin_center_eq_bot_of_outside
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    center (localJoin T L) = ⊥ := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  have h127 := source_module_nonsolvable_uniqueness D
  have hq := D.qrcHypotheses h127 hH
  have hmax := (D.lemma_3_2_3_uniqueness h127).1
  have hu := (D.lemma_3_2_3_uniqueness h127).2.2
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    rw [m.module_eq]
    exact m.thompson_centralizes_fullModule
  apply hq.center_eq_bot_of_omega_center_centralizes
    (D.simpleQTKE.evenCharacteristic T) hmax hu
  by_contra hZ
  exact hq.thompson_moves_of_noncentral_omega D.simpleQTKE hmax hu D.module_ne_bot hZ hJ

/-- The first assertion of 9.2.2 after the numerical commutator bound,
with center-freeness proved from the original source standing guard. -/
theorem fullModule_eq_omegaCenter_core_of_outside_of_commutator_le
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤
      D.fullModule) :
    D.fullModule = omegaCenterIn ((localJoin T L).pCoreIn 2) :=
  m.fullModule_eq_omegaCenter_core_of_commutator_le
    (m.localJoin_center_eq_bot_of_outside hout) hcomm

/-- The original Omega core has no L₀-fixed part under the source standing guard. -/
theorem omegaCenter_core_fixed_eq_bot_of_outside
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓
      centralizer (localOrbit T L : Set G) = ⊥ :=
  omegaCenter_core_fixed_eq_bot_of_center_eq_bot (m.localJoin_center_eq_bot_of_outside hout)

/-- The second assertion of 9.2.2 for the actual ambient interval Q ≤ S ≤ T;
only the genuine larger-module numerical input remains explicit. -/
theorem omegaCenter_eq_fullModule_inf_of_outside_of_commutator_le
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤
      D.fullModule)
    (S : Subgroup G) (hQS : (localJoin T L).pCoreIn 2 ≤ S)
    (hST : S ≤ (T : Subgroup G)) :
    omegaCenterIn S = D.fullModule ⊓ centralizer (S : Set G) :=
  m.omegaCenter_eq_fullModule_inf_of_commutator_le
    (m.localJoin_center_eq_bot_of_outside hout) hcomm S hQS hST

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
