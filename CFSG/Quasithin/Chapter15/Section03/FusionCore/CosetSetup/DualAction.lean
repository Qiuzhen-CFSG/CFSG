module

public import CFSG.Quasithin.ChapterF.Section09
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Actions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Commutator duality and elementary abelian conjugate spans

F.9.7 identifies Q/C_Q(U) with the full binary dual of U/C_U(Q).
Its equivariance and separation by linear functionals show that an element
fixing the first quotient fixes the second. Faithfulness then places V in Q.
The earlier conjugate-centralization conclusion makes ⟨V^H⟩ abelian, and its
involution generators give exponent two.

For the extraspecial reduction, Ω₁(Q) ≤ S puts ⟨Z_S^H⟩ in Z(Ω₁(Q)).
The final theorem derives elementary abelianness of both spans; it assumes
neither. The outstanding inputs are the extraspecial calculation Ω₁(Q) ≤ S
and the faithful action obtained after the generalized-Fitting argument.
The theorems use H as their ambient group. `map_localSpan_subgroupOf`
identifies these spans with the original subgroups of G.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(c)–(d), p.1143; commutator duality F.9.7, p.321.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

/-- Fixing the commutator dual quotient forces fixation of the original quotient, by F.9.7 and separation by the full linear dual. -/
theorem quotient_fixed_of_duality
    {H : Type*} [Group H] [Finite H]
    (Q U Z : Subgroup H) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hcomm : ⁅Q, U⁆ ≤ Z)
    (hZcard : Nat.card Z = 2) (h : H)
    (hfixed : ∀ q : Q,
      QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q)
        ⟨h * q * h⁻¹, (inferInstance : Q.Normal).conj_mem q q.property h⟩ =
      QuotientGroup.mk' ((centralizer (U : Set H)).subgroupOf Q) q) :
    ∀ u : U,
      QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U)
        ⟨h * u * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩ =
      QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u := by
  obtain ⟨_, e, _, he⟩ := ChapterF.lemma_F_9_7 Q U Z hZQ hZ hcomm hZcard
  intro u
  apply Additive.ofMul.injective
  apply Module.eval_apply_injective (ZMod 2)
  apply LinearMap.ext
  intro f
  obtain ⟨r, hr⟩ := e.surjective (Multiplicative.ofAdd f)
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ r
  have hi := he h q u
  rw [hfixed q, hr] at hi
  exact hi

/-- Faithfulness on U/C_U(Q) detects every subgroup centralizing the dual quotient Q/C_Q(U). -/
theorem le_of_dual_faithful
    {H : Type*} [Group H] [Finite H]
    (W Q U Z : Subgroup H) [Q.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hcomm : ⁅Q, U⁆ ≤ Z)
    (hZcard : Nat.card Z = 2)
    (hW : ⁅W, Q⁆ ≤ centralizer (U : Set H))
    (hfaithful : ∀ h : H,
      (∀ u : U,
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U)
          ⟨h * u * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩ =
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u) → h ∈ Q) :
    W ≤ Q := by
  intro h hh
  apply hfaithful h
  apply quotient_fixed_of_duality Q U Z hZQ hZ hcomm hZcard h
  intro q
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hW (commutator_mem_commutator hh q.property)

/-- A commutative span of elementary abelian two-subgroups has exponent two. -/
theorem elementary_span_of_commutative
    {G : Type*} [Group G] (V H : Subgroup G) [IsElementaryAbelian 2 V]
    [IsMulCommutative (localSpan V H)] : IsElementaryAbelian 2 (localSpan V H) := by
  have hself := le_centralizer_iff_isMulCommutative.mpr
    (inferInstance : IsMulCommutative (localSpan V H))
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  change (x : G) ^ 2 = 1
  have hx := x.property
  generalize (x : G) = a at hx ⊢
  induction hx using closure_induction with
  | mem x hx =>
      obtain ⟨h, _, v, hv, rfl⟩ := hx
      change (MulAut.conj h v) ^ 2 = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian v hv (p := 2), map_one]
  | one => simp
  | mul a b ha hb hpa hpb =>
      have hab : Commute a b := (hself hb) a ha
      rw [hab.mul_pow, hpa, hpb, one_mul]
  | inv a _ hpa => rw [inv_pow, hpa, inv_one]

/-- Earlier conjugate centralization proves both commutativity and exponent two of the span. -/
theorem elementary_span_of_weak_closure
    {G : Type*} [Group G] (V H : Subgroup G) [IsElementaryAbelian 2 V]
    (hnorm : localSpan V H ≤ normalizer (V : Set G))
    (hweak : ∀ h ∈ H, V.map (MulAut.conj h).toMonoidHom ≤ normalizer (V : Set G) →
      V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (localSpan V H) := by
  have hc : localSpan V H ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, v, hv, rfl⟩
    apply hweak h hh
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := hx
      exact hnorm (subset_closure ⟨h, hh, v, hv, rfl⟩)
    · exact mem_map_of_mem _ hv
  have hself : localSpan V H ≤ centralizer (localSpan V H : Set G) :=
    conjugateSpanBy_le (le_centralizer_iff.mp hc)
      ((le_normalizer_conjugateSpanBy V H).trans (normalizer_le_normalizer_centralizer _))
  let : IsMulCommutative (localSpan V H) := le_centralizer_iff_isMulCommutative.mp hself
  exact elementary_span_of_commutative V H

/-- The dual action places the span in Q; weak closure then makes it elementary abelian. -/
theorem elementary_span_of_dual_faithful
    {H : Type*} [Group H] [Finite H]
    (V Q U Z : Subgroup H) [Q.Normal] [U.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hcomm : ⁅Q, U⁆ ≤ Z)
    (hZcard : Nat.card Z = 2)
    (hV : ⁅V, Q⁆ ≤ centralizer (U : Set H))
    (hfaithful : ∀ h : H,
      (∀ u : U,
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U)
          ⟨h * u * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩ =
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf U) u) → h ∈ Q)
    (hQV : Q ≤ normalizer (V : Set H))
    (hweak : ∀ h : H, V.map (MulAut.conj h).toMonoidHom ≤ normalizer (V : Set H) →
      V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set H)) :
    localSpan V ⊤ ≤ Q ∧ IsElementaryAbelian 2 (localSpan V ⊤) := by
  have hVQ := le_of_dual_faithful V Q U Z hZQ hZ hcomm hZcard hV hfaithful
  have hspan : localSpan V ⊤ ≤ Q := conjugateSpanBy_le hVQ (by
    rw [Q.normalizer_eq_top])
  exact ⟨hspan, elementary_span_of_weak_closure V ⊤ (hspan.trans hQV)
    (fun h _ => hweak h)⟩


/-- The final step of 15.3.49(c), after the extraspecial calculation Ω₁(Q) ≤ S. Normality is expressed in the indicated actor H. -/
theorem span_le_center_omega
    {G : Type*} [Group G] (A H Q S : Subgroup G) [IsElementaryAbelian 2 A]
    (hHQ : H ≤ normalizer (Q : Set G)) (hAQ : A ≤ Q)
    (hAS : A ≤ centralizer (S : Set G)) (hOmegaS : omegaOneAmbient Q ≤ S) :
    localSpan A H ≤ (center (omegaOneAmbient Q)).map (omegaOneAmbient Q).subtype := by
  have hAO : A ≤ omegaOneAmbient Q := by
    rw [← omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono hAQ
  have hAC : A ≤ (center (omegaOneAmbient Q)).map (omegaOneAmbient Q).subtype := by
    intro a ha
    refine ⟨⟨a, hAO ha⟩, mem_center_iff.mpr ?_, rfl⟩
    intro k
    exact Subtype.ext (hAS ha k (hOmegaS k.property))
  have hHO : H ≤ normalizer (omegaOneAmbient Q : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh x hx
    have hm : (omegaOneAmbient Q).map (MulAut.conj h).toMonoidHom ≤ omegaOneAmbient Q := by
      apply map_le_iff_le_comap.mpr
      apply (omegaOneAmbient_le_iff _ _).mpr
      intro q hq hp
      apply (omegaOneAmbient_le_iff Q (omegaOneAmbient Q)).mp le_rfl
      · exact (hHQ hh q).mp hq
      · change (MulAut.conj h q) ^ 2 = 1
        rw [← map_pow, hp, map_one]
    exact hm (mem_map_of_mem _ hx)
  apply conjugateSpanBy_le hAC
  exact hHO.trans
    (normalizer_le_normalizer_characteristic_image (omegaOneAmbient Q) (center (omegaOneAmbient Q)))


/-- The reductions (c) and (d) with only the omega bound and faithful-action calculation left as inputs. A is Z_S; the two spans remain distinct. -/
theorem extraspecial_spans_of_omega_bound
    {H : Type*} [Group H] [Finite H]
    (V A Q Z S : Subgroup H) [Q.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hAQ : A ≤ Q) (hAS : A ≤ centralizer (S : Set H))
    (hOmegaS : omegaOneAmbient Q ≤ S)
    (hZQ : Z ≤ Q) (hZ : Z ≤ center H) (hZcard : Nat.card Z = 2)
    (hcomm : ⁅Q, localSpan A ⊤⁆ ≤ Z)
    (hfaithful : ∀ h : H,
      (∀ u : localSpan A ⊤,
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf (localSpan A ⊤))
          ⟨h * u * h⁻¹, (inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h⟩ =
        QuotientGroup.mk' ((centralizer (Q : Set H)).subgroupOf (localSpan A ⊤)) u) → h ∈ Q)
    (hQV : Q ≤ normalizer (V : Set H))
    (hweak : ∀ h : H, V.map (MulAut.conj h).toMonoidHom ≤ normalizer (V : Set H) →
      V.map (MulAut.conj h).toMonoidHom ≤ centralizer (V : Set H)) :
    localSpan A ⊤ ≤ (center (omegaOneAmbient Q)).map (omegaOneAmbient Q).subtype ∧
      IsElementaryAbelian 2 (localSpan A ⊤) ∧
      localSpan V ⊤ ≤ Q ∧ IsElementaryAbelian 2 (localSpan V ⊤) := by
  have hcenter := span_le_center_omega A ⊤ Q S (by rw [Q.normalizer_eq_top]) hAQ hAS hOmegaS
  let : IsMulCommutative (localSpan A ⊤) := .of_setLike_mul_comm
    (fun a ha b hb => setLike_mul_comm (hcenter ha) (hcenter hb))
  let : IsElementaryAbelian 2 (localSpan A ⊤) := elementary_span_of_commutative A ⊤
  have hUO : localSpan A ⊤ ≤ centralizer (omegaOneAmbient Q : Set H) := by
    intro u hu o ho
    obtain ⟨c, hc, rfl⟩ := hcenter hu
    exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨o, ho⟩)
  have hVQ : ⁅V, Q⁆ ≤ V ⊓ Q :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hQV) (commutator_le_right V Q)
  have hVO : V ⊓ Q ≤ omegaOneAmbient Q := by
    intro v hv
    exact (omegaOneAmbient_le_iff Q (omegaOneAmbient Q)).mp le_rfl v hv.2
      (elemPow_eq_one_of_isElementaryAbelian v hv.1)
  refine ⟨hcenter, inferInstance, ?_⟩
  exact elementary_span_of_dual_faithful V Q (localSpan A ⊤) Z hZQ hZ hcomm hZcard
    (hVQ.trans (hVO.trans (le_centralizer_iff.mp hUO))) hfaithful hQV hweak

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
