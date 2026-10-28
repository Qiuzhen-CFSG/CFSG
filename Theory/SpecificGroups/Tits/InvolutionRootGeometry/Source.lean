module
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryCoverage
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortRoot
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.Comparisons
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.LongRoot
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction
/-!
# The complete Tits involution fixed-parabolic source

The checked full binary involution coverage and bijective derived action
reduce every involutory automorphism to its actual long or short root class.
The first-parabolic centralizer identity and the short-root containment give
proper root parabolics after transport through the original Parrott marking.

Source: Aschbacher–Smith 16.1.4(1), p.1171; Parrott (1972), pp.672,683–684.
-/
public section
open Subgroup
namespace Tits.InvolutionRootGeometry

theorem long_centralizer_containment :
    ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s1} ≤ P := by
  let e := parrottFiniteImageEquiv
  have hconj : IsConj (parrottGenerator .s1) (e.symm atlas1600R5) := by
    have hh := e.symm.toMonoidHom.map_isConj atlas_r5_isConj_s1
    simpa only [MulEquiv.coe_toMonoidHom, e, ← parrottFiniteImageEquiv_generator,
      MulEquiv.symm_apply_apply] using hh
  obtain ⟨k,hk⟩ := isConj_iff.mp hconj
  let f : MulAut ParrottGroup := MulAut.conj k⁻¹
  refine ⟨(rootParabolic .suzuki).map f.toMonoidHom,⟨.suzuki,k⁻¹,rfl⟩,?_,?_⟩
  · have hh := f.mapSubgroup.strictMono (rootParabolic_lt_top .suzuki)
    change (rootParabolic .suzuki).map f.toMonoidHom < (⊤ : Subgroup ParrottGroup).map f.toMonoidHom at hh
    rwa [Subgroup.map_top_of_surjective f.toMonoidHom f.surjective] at hh
  · intro y hy
    let z := MulAut.conj k y
    have hz : z ∈ rootParabolic .suzuki := by
      rw [rootParabolic_suzuki_eq]
      change e z ∈ ExceptionalParabolics.first
      rw [RelativeParabolicNormalizers.first_eq_centralizer]
      apply mem_centralizer_singleton_iff.mpr
      have hh := (show Commute y (parrottGenerator .s1) from
        mem_centralizer_singleton_iff.mp hy).map (e.toMonoidHom.comp (MulAut.conj k).toMonoidHom)
      change Commute (e z) (e (k * parrottGenerator .s1 * k⁻¹)) at hh
      rw [hk,e.apply_symm_apply] at hh
      exact hh.eq
    refine ⟨z,hz,?_⟩
    change k⁻¹*(k*y*k⁻¹)*(k⁻¹)⁻¹ = y
    group

theorem short_centralizer_containment :
    ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {parrottGenerator .s4} ≤ P := by
  refine ⟨rootParabolic .linear,?_,rootParabolic_lt_top .linear,?_⟩
  · refine ⟨.linear,1,?_⟩
    rw [map_one]
    change rootParabolic .linear = (rootParabolic .linear).map (MonoidHom.id _)
    rw [Subgroup.map_id]
  · intro y hy
    rw [rootParabolic_linear_eq]
    apply ParabolicContainment.short_centralizer_le_second
    apply mem_centralizer_singleton_iff.mpr
    have hh := (show Commute y (parrottGenerator .s4) from
      mem_centralizer_singleton_iff.mp hy).map parrottFiniteImageEquiv.toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom,parrottFiniteImageEquiv_generator] using hh.eq

theorem involution_fixed_parabolic (a : MulAut ParrottGroup) (ha : orderOf a = 2) :
    ∃ P : Subgroup ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧ a.fixedSubgroup ≤ P := by
  obtain ⟨_,P,_,_,hP,hproper,hfix,_⟩ := involution_table_of_representatives
    (ReeF4.Parabolics.OuterLocal.binaryDerivedAction_bijective derivedEquiv.symm)
    binaryInvolutionCoverage long_centralizer_containment short_centralizer_containment a
    (by simpa only [ha] using pow_orderOf_eq_one a)
    (by intro h; simp [h] at ha)
  exact ⟨P,hP,hproper,hfix⟩
end Tits.InvolutionRootGeometry
