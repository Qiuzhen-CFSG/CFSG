module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.RootRecovery
public import Theory.GroupTheory.PResidual.PrimeSection
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# Generation by the conjugates of the original cubic root

A normal subgroup containing W contains every source point and hence V.
An opposite SL₂(3) factor supplies z; inversion by z supplies D. The
simple original A₆ quotient then supplies N(V), while two-perfectness
of the SL₂(3) factor supplies J and the marked rotation supplies K.
The original incidence stabilizers generate G, so the normal subgroup
is all of G. Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem normal_eq_top_of_root_le (N : Subgroup G) [N.Normal] (hWN : c.W≤N) : N=⊤ := by
  have hpoints (U:Subgroup G) (hU:U∈c.points) : U≤N := by
    obtain ⟨g,rfl⟩ := hU
    rintro _ ⟨u,hu,rfl⟩
    exact (inferInstance : N.Normal).conj_mem u (hWN hu) g
  have hVN : c.V≤N := by
    rw [←c.kernelLines_span]
    exact sSup_le (fun U hU=>hpoints U (c.pointsOn_base ▸ hU).1)
  obtain ⟨Y,hYL,hY,hne,hWY,-⟩ := c.exists_complement_fixed_opposite_cubic
  have hLN : c.oppositeFactor≤N := hWY ▸
    sup_le hWN (hpoints Y (c.cubic_in_oppositeFactor_is_point hYL hY))
  have hzN : z∈N := hLN c.involution_mem_oppositeFactor
  have hDN : c.D≤N := by
    let q := QuotientGroup.mk' N
    have hqz : q z=1 := (QuotientGroup.eq_one_iff z).mpr hzN
    intro d hd
    have hs : (q d)^2=1 := by
      have hh : q (z*d*z⁻¹*d)=1 := (QuotientGroup.eq_one_iff _).mpr (hWN (c.odd_inversion d hd))
      simpa only [map_mul,map_inv,hqz,one_mul,inv_one,mul_one,pow_two] using hh
    have hc : (q d)^3=1 := by rw [←map_pow,c.odd_cube d hd,map_one]
    rw [show 3=2+1 from rfl,pow_succ,hs,one_mul] at hc
    exact (QuotientGroup.eq_one_iff _).mp hc
  have hNVN : normalizer (c.V:Set G)≤N := by
    let M := normalizer (c.V:Set G)
    let f := NormalizerAction.quotient c.V
    let A := N.subgroupOf M
    let : A.Normal := inferInstance
    have hs : Function.Surjective f := QuotientGroup.mk'_surjective _
    let : (A.map f).Normal := Normal.map inferInstance f hs
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (NormalizerAction.Star c.V) := c.quotient_equiv_alternating_six.some.isSimpleGroup
    have he : A.map f=⊤ := by
      rcases (inferInstance : (A.map f).Normal).eq_bot_or_eq_top with hb|ht
      · have hzker : (⟨z,c.involution_normalizes_kernel⟩:M)∈f.ker :=
          A.map_eq_bot_iff.mp hb hzN
        have hzV : z∈c.V := c.quotient_kernel_eq.le hzker
        have hd := orderOf_dvd_natCard (⟨z,hzV⟩:c.V)
        rw [←c.V.orderOf_coe,h.involution,c.kernel_card] at hd
        norm_num at hd
      · exact ht
    have hk : f.ker≤A := c.quotient_kernel_eq.le.trans (subgroupOf_mono M hVN)
    have hAtop : A=⊤ := by
      have hh := congrArg (fun R : Subgroup (NormalizerAction.Star c.V)=>R.comap f) he
      rw [comap_map_eq,comap_top,sup_eq_left.mpr hk] at hh
      exact hh
    exact subgroupOf_eq_top.mp hAtop
  have hJN : c.J≤N := by
    have hp : IsPPerfect 2 c.J := GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
      c.special_model.some.symm.toMonoidHom c.special_model.some.symm.surjective
    apply le_normal_of_isPPerfect_of_le_sup_pGroup c.J N h.toCentralizerHypothesis.factorData.rightCore
      hp (isPGroup_pCoreIn 2 _)
    exact sup_le le_sup_right ((c.otherAxis_le_kernel.trans hVN).trans le_sup_left)
  have hKN : c.K≤N := sup_le hJN (zpowers_le.mpr (hNVN c.rotation_normalizes_kernel))
  apply top_unique
  rw [←c.ambient_eq_normalizers_sup]
  exact sup_le (c.complement_product ▸ sup_le hDN hKN) hNVN

theorem root_normalClosure_eq_top : normalClosure (c.W:Set G)=⊤ :=
  c.normal_eq_top_of_root_le _ le_normalClosure
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
