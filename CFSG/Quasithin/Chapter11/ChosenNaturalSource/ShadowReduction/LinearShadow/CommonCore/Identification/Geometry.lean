module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Conjugates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.GeometryReductions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Orbit
/-!
# The common axis and the intersection of the conjugate pair

The actual counterexample supplies B = C_V(V_H). The fixed-space conclusion
C_{V_H}(K) = 1 of 11.3.7 also kills C_V(K): a nontrivial T-invariant
subgroup of V meets the Sylow omega-center, which lies in V_H.

For I = ⟨V,V^h⟩, containment of K = O²(H) in I then gives I = KV,
relative normality in H, O²(I) = K, and V ∩ V^h = 1. The same argument
computes the literal conjugation kernels C_{B^h}(V) = 1 and C_P(V) = B.
A cover K ≤ I O₂(H) suffices for containment, since O₂(H) normalizes I
and K is two-perfect. That cover remains a rank-one recognition obligation;
none of these reductions asserts that the source recognition is complete.

Finally [P,K] = P upgrades P = O₂(I) to P = O₂(K). The action marking
in `Natural` will discharge this commutator premise by a matrix calculation.
All subgroups and relative normality use the original chosen ambient group.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
first two paragraphs of printed p.774, following 11.3.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

omit [Finite G] in
/-- The two existing omega-orbit definitions agree literally. -/
theorem omegaClosure_eq_omegaOrbit : omegaClosure T H = ParameterComponent.omegaOrbit T H := by
  rw [omegaClosure_eq_span, omegaCenter_eq]
  rfl

/-- The source axis is exactly the kernel of V acting on its original V_H. -/
theorem axis_eq_fixed (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H) :
    axis V H = V ⊓ centralizer (omegaClosure T H : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left V (core_centralizes_omegaClosure T H s.outside.1.1.2)
  · have hb := ParameterComponent.sylow_inf_orbit_centralizer_le_core s
      (weakClosure_not_le_core_of_counterexample s p hc)
    rw [← omegaClosure_eq_omegaOrbit] at hb
    exact le_inf inf_le_left ((inf_le_inf_right _ D.le_sylow).trans hb)

/-- Sylow omega-center detection transfers 11.3.7(3) from V_H to V. -/
theorem seed_residual_fixed_eq_bot (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    V ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  apply subgroup_eq_bot_of_central_omega_disjoint (T := T) _
    (inf_le_left.trans D.le_sylow)
  · exact (le_inf S.sylow_normalizes
      ((s.outside.1.1.2.trans (outsideResidual_normalized H)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  · apply bot_unique
    exact (le_inf (inf_le_right.trans (omegaCenter_le_closure T H))
      (inf_le_left.trans inf_le_right)).trans hf.le

/-- The central intersection vanishes once the rank-one residual lies in I. -/
theorem pair_intersection_eq_bot (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    {h : G} (hk : outsideResidual H ≤ pairGroup V h) :
    V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥ := by
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj h).toMonoidHom
  have hz : V ⊓ V.map (MulAut.conj h).toMonoidHom ≤
      centralizer (outsideResidual H : Set G) :=
    le_centralizer_iff.mp (hk.trans (sup_le_centralizer_inf_of_abelian _ _))
  exact bot_unique ((le_inf inf_le_left hz).trans (seed_residual_fixed_eq_bot s hf).le)

/-- H normalizes KV because H = KT and T normalizes both factors. -/
theorem residual_join_seed_normalized (s : Hypothesis1131At D S U₁ H) :
    H ≤ normalizer ((outsideResidual H ⊔ V : Subgroup G) : Set G) := by
  conv_lhs => rw [← outsideResidual_sup_sylow T H s.outside.1.1.2]
  apply sup_le (le_sup_left.trans (outsideResidual H ⊔ V).le_normalizer)
  exact (le_inf (s.outside.1.1.2.trans (outsideResidual_normalized H))
    S.sylow_normalizes).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Every H-conjugate of V lies in the same KV. -/
theorem pairGroup_le_residual_join_seed (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) : pairGroup V h ≤ outsideResidual H ⊔ V := by
  apply sup_le le_sup_right
  have he := mem_normalizer_iff_map_conj_eq.mp (residual_join_seed_normalized s hh)
  exact (map_mono (f := (MulAut.conj h).toMonoidHom)
    (show V ≤ outsideResidual H ⊔ V from le_sup_right)).trans he.le

/-- Residual containment identifies the entire pair group. -/
theorem pairGroup_eq_residual_join_seed (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    pairGroup V h = outsideResidual H ⊔ V :=
  le_antisymm (pairGroup_le_residual_join_seed s hh) (sup_le hk le_sup_left)

/-- The pair is normal in the selected H, rather than in the whole ambient group. -/
theorem pairGroup_normal_in_H (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    ((pairGroup V h).subgroupOf H).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (pairGroup_le s hh)).mpr
  rw [pairGroup_eq_residual_join_seed s hh hk]
  exact residual_join_seed_normalized s

/-- The actual embedded residual of I is K. -/
theorem pairGroup_residual_eq (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    outsideResidual (pairGroup V h) = outsideResidual H := by
  rw [pairGroup_eq_residual_join_seed s hh hk]
  exact embedded_pResidual_join_pGroup (outsideResidual H) V
    (isPPerfect_embedded_pResidual 2 H)
    (by let := D.elementary; exact IsElementaryAbelian.isPGroup 2 V)
    ((D.le_sylow.trans s.outside.1.1.2).trans (outsideResidual_normalized H))

/-- A cover modulo O₂(H) suffices; kernel normalization is proved from the source. -/
theorem residual_le_pairGroup_of_cover (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H)
    (hcover : outsideResidual H ≤ pairGroup V h ⊔ H.pCoreIn 2) :
    outsideResidual H ≤ pairGroup V h := by
  let I := pairGroup V h
  let Q := H.pCoreIn 2
  let N := I ⊔ Q
  have hn : N ≤ normalizer (I : Set G) :=
    sup_le I.le_normalizer (core_normalizes_pairGroup s hh)
  let : (I.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show I ≤ N from le_sup_left)).mpr hn
  have hsup : I.subgroupOf N ⊔ Q.subgroupOf N = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ N from le_sup_left) (show Q ≤ N from le_sup_right)]
    exact subgroupOf_self N
  have hquot := isPGroup_quotient_of_sup_eq_top (I.subgroupOf N) (Q.subgroupOf N)
    (isPGroup_pCoreIn 2 H).comap_subtype hsup
  have hp : IsPPerfect 2 ((outsideResidual H).subgroupOf N) :=
    (isPPerfect_embedded_pResidual 2 H).of_surjective
      (subgroupOfEquivOfLe hcover).symm.toMonoidHom
      (subgroupOfEquivOfLe hcover).symm.surjective
  have hle : (outsideResidual H).subgroupOf N ≤ I.subgroupOf N :=
    (le_pResidual_of_isPPerfect _ hp).trans (sInf_le ⟨inferInstance, hquot⟩)
  intro x hx
  exact hle (show (⟨x,hcover hx⟩ : N) ∈ (outsideResidual H).subgroupOf N from hx)

/-- H-normality of K transports its trivial fixed space to the same conjugate. -/
theorem conjugate_seed_residual_fixed_eq_bot (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    {h : G} (hh : h ∈ H) :
    V.map (MulAut.conj h).toMonoidHom ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  have he : (centralizer (outsideResidual H : Set G)).map (MulAut.conj h).toMonoidHom =
      centralizer (outsideResidual H : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp
      ((outsideResidual_normalized H).trans (normalizer_le_normalizer_centralizer _) hh)
  have hm := congrArg (map (MulAut.conj h).toMonoidHom) (seed_residual_fixed_eq_bot s hf)
  rwa [map_inf _ _ _ (MulAut.conj h).injective, he, Subgroup.map_bot] at hm

/-- The actual conjugate has no nonidentity element centralizing V. -/
theorem conjugate_inf_seed_centralizer_eq_bot (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    V.map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) = ⊥ := by
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj h).toMonoidHom
  have hx : V.map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) ≤
      centralizer (outsideResidual H : Set G) := by
    apply le_centralizer_iff.mp
    apply hk.trans
    apply sup_le (le_centralizer_iff.mpr inf_le_right)
    exact (V.map (MulAut.conj h).toMonoidHom).le_centralizer.trans (centralizer_le inf_le_left)
  exact bot_unique ((le_inf inf_le_left hx).trans
    (conjugate_seed_residual_fixed_eq_bot s hf hh).le)

/-- The literal kernel of the B^h-action on V is trivial. -/
theorem conjugate_axis_faithful (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    (axis V H).map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) = ⊥ :=
  bot_unique ((inf_le_inf_right _ (map_mono inf_le_left)).trans
    (conjugate_inf_seed_centralizer_eq_bot s hf hh hk).le)

/-- The fixed subgroup in the actual product P is the original axis B. -/
theorem pairCore_fixed_eq_axis (s : Hypothesis1131At D S U₁ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h) :
    pairCore V H h ⊓ centralizer (V : Set G) = axis V H := by
  let := D.elementary
  have hBC : axis V H ≤ centralizer (V : Set G) := inf_le_left.trans V.le_centralizer
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    obtain ⟨b,hb,a,ha,rfl⟩ := Set.mem_mul.mp
      ((pairCore_product s hh) ▸ (show x ∈ (pairCore V H h : Set G) from hx))
    have hac : a ∈ centralizer (V : Set G) := by
      have hm := (centralizer (V : Set G)).mul_mem
        ((centralizer (V : Set G)).inv_mem (hBC hb)) hc
      simpa only [inv_mul_cancel_left] using hm
    have ha1 : a = 1 := by
      have hm : a ∈ (axis V H).map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) :=
        ⟨ha,hac⟩
      rw [conjugate_axis_faithful s hf hh hk] at hm
      exact hm
    rw [ha1,mul_one]
    exact hb
  · exact le_inf le_sup_left hBC

/-- Full commutator generation absorbs the common two-core into the residual. -/
theorem pairCore_eq_residual_core_of_moved (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) (hk : outsideResidual H ≤ pairGroup V h)
    (hcore : pairCore V H h = (pairGroup V h).pCoreIn 2)
    (hmoved : ⁅pairCore V H h, outsideResidual H⁆ = pairCore V H h) :
    pairCore V H h = (outsideResidual H).pCoreIn 2 := by
  have hPK : pairCore V H h ≤ outsideResidual H := by
    rw [← hmoved]
    exact le_normalizer_iff_commutator_le_right.mp
      ((pairCore_le_pairGroup h).trans ((pairGroup_le s hh).trans (outsideResidual_normalized H)))
  have he := pCoreIn_embedded_pResidual_eq_of_core_le 2 (pairGroup V h) (by
    rw [← hcore]
    change pairCore V H h ≤ outsideResidual (pairGroup V h)
    rwa [pairGroup_residual_eq s hh hk])
  change (outsideResidual (pairGroup V h)).pCoreIn 2 = (pairGroup V h).pCoreIn 2 at he
  rw [pairGroup_residual_eq s hh hk, ← hcore] at he
  exact he.symm

/-- The source conjugator may be chosen inside I, as required by E.2.10,
without changing either V^h or B^h. The original outside condition survives. -/
theorem exists_internal_pair_conjugator (s : Hypothesis1131At D S U₁ H)
    {h : G} (hh : h ∈ H) (hm : h ∉ normalizer (L : Set G))
    (hk : outsideResidual H ≤ pairGroup V h) :
    ∃ k : G, k ∈ outsideResidual H ∧ k ∈ pairGroup V h ∧
      k ∉ normalizer (L : Set G) ∧
      V.map (MulAut.conj k).toMonoidHom = V.map (MulAut.conj h).toMonoidHom ∧
      (axis V H).map (MulAut.conj k).toMonoidHom =
        (axis V H).map (MulAut.conj h).toMonoidHom := by
  have hprod : (H : Set G) =
      (outsideResidual H : Set G) * ((T : Subgroup G) : Set G) := by
    conv_lhs => rw [← outsideResidual_sup_sylow T H s.outside.1.1.2]
    exact coe_mul_of_right_le_normalizer_left _ _
      (s.outside.1.1.2.trans (outsideResidual_normalized H))
  obtain ⟨k,hkK,t,ht,rfl⟩ := Set.mem_mul.mp (hprod ▸ (show h ∈ (H : Set G) from hh))
  have htB : t ∈ normalizer (axis V H : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨S.sylow_normalizes ht,
      ((s.outside.1.1.2.trans H.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) ht⟩
  have hconj (A : Subgroup G) (htA : t ∈ normalizer (A : Set G)) :
      A.map (MulAut.conj k).toMonoidHom = A.map (MulAut.conj (k * t)).toMonoidHom := by
    have hcomp : (MulAut.conj k).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (k * t)).toMonoidHom := by
      ext a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        _root_.mul_inv_rev]
      group
    have htE : A.map (MulAut.conj t).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp htA
    rw [← hcomp, ← Subgroup.map_map, htE]
  refine ⟨k,hkK,hk hkK,?_,hconj V (S.sylow_normalizes ht),hconj _ htB⟩
  intro hkM
  exact hm ((normalizer (L : Set G)).mul_mem hkM (D.sylow_normalizes_component ht))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
