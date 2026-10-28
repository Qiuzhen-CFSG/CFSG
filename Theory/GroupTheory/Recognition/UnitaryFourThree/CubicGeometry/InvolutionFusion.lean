module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentStabilizer
public import Theory.GroupTheory.OddKernelInvolutionConjugacy
public import Theory.GroupTheory.CommutingFactorSwapConjugacy
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
/-!
# Internal fusion of the source Sylow involutions outside the core

The actual N(V)/V is A₆ and V has odd order, so all its involutions
are conjugate in N(V). An involution of the original Sylow two-subgroup
outside Q interchanges the quaternion factors. Its same-core-coset
representative in N(X) is an involution; the commuting-factor calculation
conjugates it by Q into ⟨z,t⟩≤N(V).
Consequently every such involution is conjugate to z by an element of
the actual component stabilizer. Ambient fusion alone is not used to
claim that a conjugator belongs to this subgroup.
Source: Aschbacher, Sporadic Groups (1994),45.3–45.5,45.9–45.11, pp.243–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem kernel_normalizer_involutions_conjugate (a b : G)
    (ha : a ∈ normalizer (c.V : Set G)) (hb : b ∈ normalizer (c.V : Set G))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    ∃ g ∈ normalizer (c.V : Set G), g*a*g⁻¹=b := by
  let M := normalizer (c.V : Set G)
  let f := NormalizerAction.quotient c.V
  let aM : M := ⟨a,ha⟩
  let bM : M := ⟨b,hb⟩
  have hka : Nat.card f.ker = 81 := by
    rw [c.quotient_kernel_eq, Nat.card_congr (subgroupOfEquivOfLe c.V.le_normalizer).toEquiv]
    exact c.kernel_card
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by rw [hka]; decide
  have haM : orderOf aM = 2 := (orderOf_coe aM).symm.trans ha2
  have hbM : orderOf bM = 2 := (orderOf_coe bM).symm.trans hb2
  obtain ⟨e⟩ := c.quotient_equiv_alternating_six
  have he := AlternatingSix.ShadowLocal.involutions_isConj (e (f aM)) (e (f bM))
    ((e.orderOf_eq _).trans (orderOf_map_involution_of_odd_kernel f hk haM))
    ((e.orderOf_eq _).trans (orderOf_map_involution_of_odd_kernel f hk hbM))
  have hc : IsConj (f aM) (f bM) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj he
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (isConj_of_map_involutions_of_odd_kernel f (QuotientGroup.mk'_surjective _) hk haM hbM hc)
  exact ⟨g,g.property,congrArg Subtype.val hg⟩

theorem kernel_normalizer_involution_fused_in_component (a : G)
    (ha : a ∈ normalizer (c.V : Set G)) (ha2 : orderOf a = 2) :
    ∃ g ∈ c.componentStabilizer, g*z*g⁻¹=a := by
  obtain ⟨g,hg,he⟩ := c.kernel_normalizer_involutions_conjugate z a
    c.involution_normalizes_kernel ha h.involution ha2
  exact ⟨g,c.kernel_normalizer_le_componentStabilizer hg,he⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration



namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem outside_core_involution_conjugate_kernel_normalizer (R : RootPair z)
    (v : G) (hv : v∈R.T) (hv2 : orderOf v=2) (hvQ : v∉core z) :
    ∃ b∈core z, b⁻¹*v*b ∈ normalizer (c.V:Set G) := by
  have hvpow : v^2=1 := hv2 ▸ pow_orderOf_eq_one v
  have hvR : v∈R.R := (R.involution_mem_R_or_core h v hv hv2).resolve_right hvQ
  let : IsElementaryAbelian 2 (zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hvpow
  obtain ⟨E,hvE,hET,hEE,hEc⟩ := R.elementary_in_R_le_plane h (zpowers v) (zpowers_le.mpr hvR)
  obtain ⟨t,ht,ht2,htQ,hvt⟩ := R.cubic_reflection_in_plane_coset h c.X
    (h.cubic_sylow_image_card P) (map_subtype_le _) E ⟨hET,hEE,hEc⟩ v (hvE (mem_zpowers v)) hvQ
  let d := h.toCentralizerHypothesis.factorData
  have hswap := (R.T_involution_swaps_core_factors h t ht.1 ht2 htQ).1
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hvpow)
  have hvt' : v*t⁻¹∈d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,hti]
    simpa only [hvi] using hvt
  obtain ⟨b,hb,hbcon⟩ := involution_swap_coset_conjugate_intersection d.leftCore d.rightCore
    (fun b hb c hc => d.factors_commute h.involution b (pCoreIn_le 2 d.left hb)
      c (pCoreIn_le 2 d.right hc)) t ht2 hswap v hvpow hvt'
  refine ⟨b, (d.core_span h.involution) ▸ (show b∈d.leftCore⊔d.rightCore from mem_sup_left hb), ?_⟩
  have hle : d.leftCore⊓d.rightCore ⊔ zpowers t ≤ normalizer (c.V:Set G) := by
    refine sup_le ?_ ?_
    · rw [d.core_intersection h.involution]
      exact zpowers_le.mpr c.involution_normalizes_kernel
    · exact zpowers_le.mpr (CubicNormalizer.normalizer_normalizes_oddKernel c.X ht.2)
  exact hle hbcon

theorem outside_core_involution_fused_in_component (R : RootPair z)
    (v : G) (hv : v∈R.T) (hv2 : orderOf v=2) (hvQ : v∉core z) :
    ∃ g∈c.componentStabilizer, g*z*g⁻¹=v := by
  obtain ⟨b,hb,hbc⟩ := c.outside_core_involution_conjugate_kernel_normalizer R v hv hv2 hvQ
  have hbo : orderOf (b⁻¹*v*b)=2 := by
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj b⁻¹).orderOf_eq v).trans hv2
  obtain ⟨g,hg,he⟩ := c.kernel_normalizer_involution_fused_in_component (b⁻¹*v*b) hbc hbo
  refine ⟨b*g,c.componentStabilizer.mul_mem (c.core_le_componentStabilizer hb) hg,?_⟩
  calc
    _ = b*(g*z*g⁻¹)*b⁻¹ := by group
    _ = v := by rw [he]; group
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
