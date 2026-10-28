module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Outside involutions in minus-extraspecial A₅ extensions

Let Q be a self-centralizing normal subgroup isomorphic to Q₈ ∘ D₈,
with H/Q isomorphic to A₅. The five-point action has kernel Q: an element
acting inner on Q belongs to Q C_H(Q) = Q. Its sign factors through A₅,
where perfectness makes it trivial. Thus every outside involution induces
a nonidentity even involution on the five singular points.

First conjugate two quotient involutions together in A₅ and lift the
conjugator to H. Their difference in Q is a twisted cocycle for conjugation
by one of the involutions. The model cocycle theorem makes this difference
a coboundary, supplying a conjugator in Q. No splitting of the extension
or simplicity of H is required. The two-core specialization is the interface
for local characteristic-two applications.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 46.11, printed p.255.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside
variable {H : Type*} [Group H]

private def modelAction (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model) : H →* MulAut Model :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

private noncomputable def pointAction (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model) :
    H →* Equiv.Perm (Fin 5) := fivePointAction.comp (modelAction Q e)

private theorem pointAction_kernel (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) : (pointAction Q e).ker = Q := by
  have hi : (MulAut.innerSubgroup Model).comap (MulAut.congr e).toMonoidHom =
      MulAut.innerSubgroup Q := by
    rw [← MulAut.map_innerSubgroup_congr e,
      comap_map_eq_self_of_injective (MulAut.congr e).injective]
  unfold pointAction modelAction
  rw [← MonoidHom.comap_ker, action_kernel]
  change (MulAut.innerSubgroup Model).comap
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) = Q
  rw [← comap_comap, hi, MulAut.conjNormal_comap_innerSubgroup, sup_eq_left.mpr hc]

private theorem pointAction_even (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5)) (u : H) :
    Equiv.Perm.sign (pointAction Q e u) = 1 := by
  let f := pointAction Q e
  let fbar := QuotientGroup.lift Q f (pointAction_kernel Q e hc).symm.le
  let s := (Equiv.Perm.sign.comp fbar).comp eA.symm.toMonoidHom
  have hker : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ s.ker := by
    rw [← commutator_alternatingGroup_eq_top (by simp)]
    exact Abelianization.commutator_subset_ker s
  have hs := hker (mem_top (eA (QuotientGroup.mk' Q u)))
  change s (eA (QuotientGroup.mk' Q u)) = 1 at hs
  simpa only [s, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, fbar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk', f] using hs

private theorem same_coset_fusion (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (u v : H) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huQ : u ∉ Q)
    (huv : QuotientGroup.mk' Q v = QuotientGroup.mk' Q u) : IsConj u v := by
  let a := modelAction Q e u
  have ha : a ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA u
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    apply huQ
    rw [← pointAction_kernel Q e hc]
    exact heq
  have hdmem : v * u⁻¹ ∈ Q := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp huv
  let d : Q := ⟨v * u⁻¹, hdmem⟩
  have hd : d * MulAut.conjNormal u d = 1 := by
    apply Subtype.ext
    change (v * u⁻¹) * (u * (v * u⁻¹) * u⁻¹) = 1
    calc
      _ = v ^ 2 * (u ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hu, hv]; simp
  have hd' : e d * a (e d) = 1 := by
    change e d * e (MulAut.conjNormal u (e.symm (e d))) = 1
    rw [e.symm_apply_apply, ← map_mul, hd, map_one]
  obtain ⟨q, hq⟩ := cocycle_eq_coboundary a ha heven hne (e d) hd'
  let qQ := e.symm q
  have hdQ : d = qQ * (MulAut.conjNormal u qQ)⁻¹ := by
    apply e.injective
    change e d = q * (e (MulAut.conjNormal u (e.symm q)))⁻¹ at hq
    simpa only [map_mul, map_inv, qQ, MulEquiv.apply_symm_apply] using hq
  have hdH := congrArg Subtype.val hdQ
  change v * u⁻¹ = (qQ : H) * (u * (qQ : H) * u⁻¹)⁻¹ at hdH
  apply isConj_iff.mpr
  refine ⟨qQ, ?_⟩
  calc
    (qQ : H) * u * (qQ : H)⁻¹ =
        ((qQ : H) * (u * (qQ : H) * u⁻¹)⁻¹) * u := by group
    _ = v := by rw [← hdH]; group

/-- In a self-centralizing minus-extraspecial normal subgroup extension by A₅,
all involutions outside the normal subgroup are conjugate. -/
public theorem outside_involutions_isConj (Q : Subgroup H) [Q.Normal]
    (hQ : Nonempty (Q ≃* Model)) (hc : centralizer (Q : Set H) ≤ Q)
    (hA : Nonempty ((H ⧸ Q) ≃* alternatingGroup (Fin 5)))
    (u v : H) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huQ : u ∉ Q) (hvQ : v ∉ Q) : IsConj u v := by
  obtain ⟨e⟩ := hQ
  obtain ⟨eA⟩ := hA
  let π := QuotientGroup.mk' Q
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  have ho (w : H) (hw : w ^ 2 = 1) (hwQ : w ∉ Q) : orderOf (eA (π w)) = 2 := by
    rw [eA.orderOf_eq]
    exact orderOf_eq_prime (by rw [← map_pow, hw, map_one])
      (fun hh => hwQ ((QuotientGroup.eq_one_iff w).mp hh))
  have hconj := alternatingGroup.five_involutions_isConj (eA (π u)) (eA (π v))
    (ho u hu2 huQ) (ho v hv2 hvQ)
  have hconj' : IsConj (π u) (π v) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      eA.symm.toMonoidHom.map_isConj hconj
  obtain ⟨gbar, hgbar⟩ := isConj_iff.mp hconj'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gbar
  let w := g * u * g⁻¹
  have hw2 : w ^ 2 = 1 := by
    change (MulAut.conj g u) ^ 2 = 1
    rw [← map_pow, hu2, map_one]
  have hwQ : w ∉ Q := by
    intro hwQ
    apply hvQ
    apply (QuotientGroup.eq_one_iff v).mp
    change π v = 1
    rw [← hgbar, ← map_inv, ← map_mul, ← map_mul]
    exact (QuotientGroup.eq_one_iff w).mpr hwQ
  have hwv : π v = π w := by
    simpa only [w, map_mul, map_inv] using hgbar.symm
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans (same_coset_fusion Q e hc eA w v hw2 hv2 hwQ hwv)

/-- The two-core formulation used by local characteristic-two consumers. -/
public theorem pCore_outside_involutions_isConj [Finite H]
    (hQ : Nonempty (pCore 2 H ≃* Model))
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hA : Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)))
    (u v : H) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huQ : u ∉ pCore 2 H) (hvQ : v ∉ pCore 2 H) : IsConj u v :=
  outside_involutions_isConj (pCore 2 H) hQ hc hA u v hu hv huQ hvQ
end MinusExtraspecial
