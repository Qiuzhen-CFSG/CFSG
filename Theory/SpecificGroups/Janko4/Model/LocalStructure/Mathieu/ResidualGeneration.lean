module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import Theory.GroupTheory.PResidual.FiniteLocalPair

/-!
# Perfect-residual generation in the native J₄ model

The actual Mathieu local subgroup and each native involution centralizer
have two-group quotient by their perfect residuals. Their two-residuals
therefore agree with their perfect residuals. The native Sylow geometry
provides a Mathieu local subgroup which generates J₄ together with the
centralizer of a nontrivial Sylow-central involution. The common-Sylow
residual theorem then gives generation by the two perfect residuals.

Perfectness of the ambient model is inherited from the component in the
application; no independent simplicity or order certificate is needed.
This is the model generation step in Aschbacher--Smith 4.4.3, printed p.623.
Native matrix and subgroup certificates retain their ATLAS attribution
through the imported local-structure modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

private theorem residual_le_twoResidual {X : Type*} [Group X] [Finite X] :
    solvableResidual X ≤ pResidual 2 X := by
  let : Group.IsNilpotent (X ⧸ pResidual 2 X) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact solvableResidual_le_of_solvable_quotient _

private theorem residuals_eq_of_quotient_two {X : Type*} [Group X] [Finite X]
    (h : IsPGroup 2 (X ⧸ solvableResidual X)) :
    pResidual 2 X = solvableResidual X :=
  le_antisymm (sInf_le ⟨inferInstance,h⟩) residual_le_twoResidual

private theorem quotient_two_of_perfect_normal {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] [Group.IsPerfect N]
    (h : IsPGroup 2 (X ⧸ N)) : IsPGroup 2 (X ⧸ solvableResidual X) := by
  let f := QuotientGroup.map N (solvableResidual X) (MonoidHom.id X)
    (le_solvableResidual_of_isPerfect N)
  exact h.of_surjective f (QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id X) QuotientGroup.mk_surjective _)

private theorem quotient_two_of_two_kernel {X Y : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hY : IsPGroup 2 (Y ⧸ solvableResidual Y)) :
    IsPGroup 2 (X ⧸ solvableResidual X) := by
  let D := solvableResidual X
  let E := solvableResidual Y
  have he : D.map f = E := map_solvableResidual_eq f hf
  let q := QuotientGroup.map D E f (map_le_iff_le_comap.mp he.le)
  have hker : q.ker = f.ker.map (QuotientGroup.mk' D) := by
    rw [QuotientGroup.ker_map,←he,comap_map_eq,Subgroup.map_sup,
      QuotientGroup.map_mk'_self,bot_sup_eq]
  have hq : IsPGroup 2 q.ker := hker ▸ hk.map (QuotientGroup.mk' D)
  exact ((hY.to_subgroup ⊤).comap_of_ker_isPGroup q hq).of_equiv
    ((MulEquiv.subgroupCongr (comap_top q)).trans topEquiv)

private theorem residuals_eq_of_equiv {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (e : X ≃* Y)
    (h : pResidual 2 Y = solvableResidual Y) : pResidual 2 X = solvableResidual X := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    map_solvableResidual_eq e.toMonoidHom e.surjective,h]

private theorem m24_perfect : Group.IsPerfect Sporadic.Mathieu.M24 := by
  let := Sporadic.Mathieu.m24_isSimpleGroup
  refine ⟨(inferInstance : (_root_.commutator Sporadic.Mathieu.M24).Normal).eq_bot_or_eq_top.resolve_left ?_⟩
  intro hb
  let := (commutator_eq_bot_iff Sporadic.Mathieu.M24).mp hb
  have hp := Group.is_simple_iff_prime_card.mp Sporadic.Mathieu.m24_isSimpleGroup
  rw [Sporadic.Mathieu.m24_order] at hp
  norm_num at hp

/-- The two-residual of the actual Mathieu local group is its perfect residual. -/
theorem mathieu_local_residuals :
    pResidual 2 SylowCore.Local = solvableResidual SylowCore.Local := by
  let q := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' (Cardinality.localKernel matrixA_mul_self matrixB_pow_four))
  have hq : Function.Surjective q := (localQuotientEquivM24 _ _).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = Cardinality.localKernel matrixA_mul_self matrixB_pow_four := by
    rw [MonoidHom.ker_comp_of_injective _ _ (localQuotientEquivM24 _ _).injective,
      QuotientGroup.ker_mk']
  let := m24_perfect
  exact pResidual_eq_solvableResidual_of_perfect_image q hq
    (hk.symm ▸ IsPGroup.of_card (n := 11) (by simpa using (Cardinality.localKernel_card matrixA_mul_self matrixB_pow_four)))

private theorem first_residuals :
    pResidual 2 InvolutionCentralizers.First.centralizer =
      solvableResidual InvolutionCentralizers.First.centralizer := by
  let C := InvolutionCentralizers.First.centralizer
  let f := InvolutionCentralizers.First.centralizerExtension.rightHom
  have hk : IsPGroup 2 f.ker := by
    rw [InvolutionCentralizers.First.QuotientExtension.centralizerProjection_ker]
    exact pCore_isPGroup
  let E := InvolutionCentralizers.First.QuotientExtension.coverSubgroup
  let e : E ≃* Sporadic.Mathieu.M22TripleCover := subgroupOfEquivOfLe
    OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.derivedGroup_le_actionGroup
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hE : IsPGroup 2 (_ ⧸ E) := (IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr InvolutionCentralizers.First.QuotientExtension.coverQuotientEquiv.toEquiv]
    norm_num))
  exact residuals_eq_of_quotient_two (quotient_two_of_two_kernel f
    InvolutionCentralizers.First.centralizerExtension.rightHom_surjective hk
    (quotient_two_of_perfect_normal E hE))

private theorem second_residuals :
    pResidual 2 InvolutionCentralizers.Second.ambientCentralizer =
      solvableResidual InvolutionCentralizers.Second.ambientCentralizer := by
  let f := InvolutionCentralizers.Second.ambientExtension.rightHom
  let := InvolutionCentralizers.Second.ambientKernel_elementary
  have hk : IsPGroup 2 f.ker := IsElementaryAbelian.isPGroup 2 _
  let : Group.IsPerfect Sporadic.Mathieu.M22 := Group.IsPerfect.ofSurjective
    (f := Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (center Sporadic.Mathieu.M22TripleCover)))
    (Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv.surjective.comp
      (QuotientGroup.mk'_surjective _))
  let : Group.IsPerfect (MulAut.innerSubgroup Sporadic.Mathieu.M22) :=
    Group.IsPerfect.range MulAut.conj
  have ho : IsPGroup 2 (MulAut.Outer Sporadic.Mathieu.M22) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one] using
      Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)
  exact residuals_eq_of_quotient_two (quotient_two_of_two_kernel f
    InvolutionCentralizers.Second.ambientExtension.rightHom_surjective hk
    (quotient_two_of_perfect_normal (MulAut.innerSubgroup _) ho))

/-- Both native involution centralizers have two-group quotient by their perfect residual. -/
theorem involution_centralizer_residuals (z : Model) (hz : orderOf z = 2) :
    pResidual 2 (centralizer ({z} : Set Model)) =
      solvableResidual (centralizer ({z} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    exact residuals_eq_of_equiv e first_residuals
  · obtain ⟨e⟩ := h
    exact residuals_eq_of_equiv e second_residuals

/-- The actual Mathieu seed and the actual involution centralizer generate
through their perfect residuals, with a common ambient Sylow subgroup. -/
theorem exists_sylow_mathieu_residual_seed [Group.IsPerfect Model] (S : Sylow 2 Model) :
    ∃ R : Subgroup Model, (S : Subgroup Model) ≤ R ∧
      Nonempty (R ≃* SylowCore.Local) ∧
      (∀ alpha : MulAut Model, (S : Subgroup Model).map alpha.toMonoidHom = S →
        R.map alpha.toMonoidHom = R) ∧
      ∀ z : Model, orderOf z = 2 → z ∈ centralizer (S : Set Model) →
        (solvableResidual R).map R.subtype ⊔
          (solvableResidual (centralizer ({z} : Set Model))).map
            (centralizer ({z} : Set Model)).subtype = ⊤ := by
  obtain ⟨R,hSR,⟨e⟩,hinv,hgen⟩ := exists_sylow_mathieu_seed S
  refine ⟨R,hSR,⟨e⟩,hinv,?_⟩
  intro z hz hc
  have hSC : (S : Subgroup Model) ≤ centralizer ({z} : Set Model) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx)
  have hne : z ≠ 1 := by intro h; rw [h,orderOf_one] at hz; omega
  have hp : pResidual 2 Model = ⊤ := top_unique (by
    simpa only [solvableResidual_eq_top] using (residual_le_twoResidual (X := Model)))
  have hh := pResidual_eq_sup_of_finite_sylow_pair R (centralizer ({z} : Set Model))
    (S : Subgroup Model) (S.subtype hSR) (S.subtype hSC)
    (map_subgroupOf_eq_of_le hSR) (map_subgroupOf_eq_of_le hSC)
    ((sup_comm _ _).trans (hgen z hne hc))
  rw [hp,residuals_eq_of_equiv e mathieu_local_residuals,
    involution_centralizer_residuals z hz] at hh
  exact hh.symm

end Janko4.LocalStructure
