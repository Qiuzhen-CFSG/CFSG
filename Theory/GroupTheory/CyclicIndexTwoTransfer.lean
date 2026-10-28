module

public import Theory.GroupTheory.GeneralizedThompsonTransfer
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Transfer through a cyclic subgroup of index two

Thompson transfer fuses every involution into the cyclic subgroup of index
two in a Sylow two-subgroup when there is no ambient subgroup of index two.
Its unique involution therefore represents the only ambient class.

If that involution is central in the ambient group and every element outside
the cyclic subgroup is an involution, Thompson transfer excludes all those
elements from the two-residual. Its Sylow subgroup is then cyclic, so the
cyclic-Sylow normal-complement theorem makes the residual odd. This proves
the actual normal-complement step in Aschbacher–Smith I.4.3, pp.416–417.
-/

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

/-- The cyclic-index-two transfer implication for all ambient involutions. -/
public theorem involutions_conjugate_of_cyclic_index_two
    (T : Sylow 2 G) (R : Subgroup T) [IsCyclic R] (hindex : R.index = 2)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (z : R) (hz : orderOf z = 2) :
    ∀ u : G, orderOf u = 2 → IsConj u (z : G) := by
  intro u hu
  obtain ⟨v, huv⟩ := T.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hu)
  have hv : orderOf v = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huv
    have he : (MulAut.conj g) u = (v : G) := hg
    rw [← Subgroup.orderOf_coe v, ← he, MulEquiv.orderOf_eq, hu]
  obtain ⟨w, hvw, hw⟩ := T.exists_isConj_mem_of_index_two hno R hindex v hv
  have hwo : orderOf (⟨w, hw⟩ : R) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hvw
    have he : (MulAut.conj g) (v : G) = (w : G) := hg
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, ← he,
      MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hv]
  have hwz : (⟨w, hw⟩ : R) = z := IsCyclic.eq_of_orderOf_eq_two hwo hz
  have he : (w : G) = (z : G) := congrArg (fun a : R => (a : G)) hwz
  exact huv.trans (he ▸ hvw)

/-- The central cyclic involution forces a normal two-complement. -/
public theorem normalTwoComplement_of_cyclic_index_two
    (T : Sylow 2 G) (R : Subgroup T) [IsCyclic R] (hindex : R.index = 2)
    (z : R) (hz : orderOf z = 2) (hzcentral : (z : G) ∈ center G)
    (hout : ∀ v : T, v ∉ R → orderOf v = 2) :
    HasNormalPComplement 2 G := by
  have hres : ∀ v : T, (v : G) ∈ pResidual 2 G → v ∈ R := by
    intro v hv
    by_contra hnot
    apply T.involution_not_mem_twoResidual_of_no_conjugate R hindex (v : G)
      (by simpa using hout v hnot) ?_ hv
    intro w hconj hw
    have hwo : orderOf (⟨w, hw⟩ : R) = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      have he : (MulAut.conj g) (v : G) = (w : G) := hg
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, ← he,
        MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hout v hnot]
    have he : (w : G) = (z : G) := congrArg (fun a : R => (a : G))
      (IsCyclic.eq_of_orderOf_eq_two hwo hz)
    rw [he] at hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hvz : (v : G) = (z : G) := by
      calc
        (v : G) = g⁻¹ * (g * (v : G) * g⁻¹) * g := by group
        _ = g⁻¹ * (z : G) * g := by rw [hg]
        _ = (z : G) := by
          rw [(mem_center_iff.mp hzcentral g⁻¹)]
          simp
    exact hnot ((Subtype.ext hvz : v = (z : T)) ▸ z.property)
  let E := pResidual 2 G
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal E
  let f : S →* R :=
    { toFun := fun s => ⟨⟨s.val.val, by
        exact hS.le s.property⟩, hres _ s.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : R => (r : G)) h
  have hScyc : IsCyclic S := isCyclic_of_injective f hf
  have hEodd : Odd (Nat.card E) := by
    have ho := S.odd_card_twoResidual_of_isCyclic hScyc
    rw [(pResidual_eq_top_iff 2 E).mpr (isPPerfect_pResidual 2), card_top] at ho
    exact ho
  exact ⟨E, inferInstance, Nat.coprime_two_left.mpr hEodd,
    isPGroup_quotient_pResidual 2⟩
end Sylow
