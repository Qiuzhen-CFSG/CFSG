module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.LocalQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The triality tensor kernel

Tensor the actual first spin representation with a real representation on
which `Q1` acts trivially and `c = ψ₂(sπ)` acts as minus identity. The paired
minus actions of `k2 = c * z1` kill `K`. Contracting with one nonzero natural
coordinate shows that the tensor kernel meets `Q1` in `K1`. Normality then
puts the kernel in the preimage of the extraspecial centralizer, namely
`K ⊔ ⟨z1⟩`; the minus action of `z1` removes the remaining coset.

This proves the kernel calculation for any nonzero natural factor and gives
a faithful action of the actual local quotient. The natural-factor hypotheses
are explicit: their discharge for the source coordinate-halfspace module
belongs to final assembly, so this module alone does not assert unconditional
Lemma 27.5. No kernel or equivariance conclusion is assumed.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.5(2–4), printed p. 147.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct commutatorElement
open Atlas.Fischer
namespace Sporadic.Monster.Construction.TrialitySpin.TensorKernel
open SpinAction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (ρ : Representation ℝ N1 V)

/-- The genuine tensor product with the constructed spin action. -/
def representation : Representation ℝ N1 (V ⊗[ℝ] SpinSpace) :=
  ρ.tprod SpinAction.representation

private theorem tmul_cancel_left {v : V} (hv : v ≠ 0) {s t : SpinSpace}
    (h : v ⊗ₜ[ℝ] s = v ⊗ₜ[ℝ] t) : s = t := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  have he := congrArg (fun x => TensorProduct.lid ℝ SpinSpace
    (TensorProduct.map f (LinearMap.id : SpinSpace →ₗ[ℝ] SpinSpace) x)) h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    hf, one_smul] using he

variable (hQ : ∀ q : N1, q.val ∈ Q1 → ρ q = 1)
variable (hc : ρ c = -1)
include hQ

/-- The central involution is trivial on any natural factor killed by `Q1`. -/
theorem natural_z : ρ z = 1 := hQ z z1N_mem_Q1

theorem natural_kOne : ρ kOne = 1 :=
  hQ kOne (K1_le_Q1 (Subgroup.mem_zpowers k1))

include hc in
theorem natural_kTwo : ρ kTwo = -1 := by
  rw [kTwo_eq_c_mul_z, map_mul, hc, natural_z ρ hQ, mul_one]

theorem representation_kOne : representation ρ kOne = 1 := by
  apply TensorProduct.ext'
  intro v s
  simp only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
    natural_kOne ρ hQ, SpinAction.representation_kOne, Module.End.one_apply]

include hc in
theorem representation_kTwo : representation ρ kTwo = 1 := by
  apply TensorProduct.ext'
  intro v s
  simp only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
    natural_kTwo ρ hQ hc, SpinAction.representation_kTwo, LinearMap.neg_apply,
    Module.End.one_apply, TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

include hc in
theorem K_le_kernel : K.subgroupOf N1 ≤ (representation ρ).ker := by
  intro g hg
  rcases (mem_K_iff g.val).mp hg with h | h | h | h
  · have he : g = 1 := Subtype.ext h
    rw [he]
    exact (representation ρ).map_one
  · have he : g = kOne := Subtype.ext h
    exact he ▸ representation_kOne ρ hQ
  · have he : g = kTwo := Subtype.ext h
    exact he ▸ representation_kTwo ρ hQ hc
  · have he : g = kOne * kTwo := (Subtype.ext h).trans kThree_eq_kOne_mul_kTwo
    change representation ρ g = 1
    rw [he, map_mul, representation_kOne ρ hQ, representation_kTwo ρ hQ hc, one_mul]

/-- The natural factor is fixed on `Q1`, so a single coordinate contraction
recovers the spin action from the tensor action. -/
theorem on_Q1_kernel_iff [Nontrivial V] (q : N1) (hq : q.val ∈ Q1) :
    representation ρ q = 1 ↔ q.val ∈ K1 := by
  have hs : SpinAction.representation q = 1 ↔ q.val ∈ K1 := by
    rw [SpinAction.representation_eq_one_iff, ← Q1_inf_J_eq_K1]
    exact ⟨fun h => ⟨hq,h⟩, fun h => h.2⟩
  rw [← hs]
  constructor
  · intro h
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    apply LinearMap.ext
    intro s
    apply tmul_cancel_left hv
    have he := congrArg (fun f : Module.End ℝ (V ⊗[ℝ] SpinSpace) => f (v ⊗ₜ[ℝ] s)) h
    simpa only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
      hQ q hq, Module.End.one_apply] using he
  · intro h
    apply TensorProduct.ext'
    intro v s
    simp only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
      hQ q hq, h, Module.End.one_apply]

theorem representation_z : representation ρ z = -1 := by
  apply TensorProduct.ext'
  intro v s
  simp only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
    natural_z ρ hQ, SpinAction.representation_z_eq, Module.End.one_apply,
    LinearMap.neg_apply, TensorProduct.tmul_neg]

omit hQ in
private theorem neg_spin_ne_self : ∃ s : SpinSpace, -s ≠ s := by
  let : Nontrivial SpinSpace := Module.nontrivial_of_finrank_pos (by
    rw [finrank_spinSpace]; norm_num)
  obtain ⟨s, hs⟩ := exists_ne (0 : SpinSpace)
  refine ⟨s, fun h => hs ?_⟩
  have he : (2 : ℝ) • s = 0 := by
    rw [two_smul]
    conv_lhs => lhs; rw [← h]
    exact neg_add_cancel s
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem z_not_mem_kernel [Nontrivial V] : z ∉ (representation ρ).ker := by
  intro h
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  obtain ⟨s,hs⟩ := neg_spin_ne_self
  apply hs
  apply tmul_cancel_left hv
  have he := congrArg (fun f : Module.End ℝ (V ⊗[ℝ] SpinSpace) => f (v ⊗ₜ[ℝ] s)) h
  simpa only [representation_z ρ hQ, LinearMap.neg_apply, Module.End.one_apply,
    TensorProduct.tmul_neg] using he

omit hQ in
private theorem mem_zpowers_z1_iff (g : N) :
    g ∈ Subgroup.zpowers z1N ↔ g = 1 ∨ g = z1N := by
  classical
  have hn : z1N ≠ 1 := fun h => z1N_not_mem_K (h ▸ K.one_mem)
  have ho : orderOf z1N = 2 := orderOf_eq_prime z1N_sq hn
  have hf : IsOfFinOrder z1N := orderOf_pos_iff.mp (by omega)
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, pow_zero _⟩
    · exact ⟨1, by decide, pow_one _⟩

include hc in
/-- Source 27.5(3), conditional only on the two independently constructed
natural-factor actions. No tensor-kernel conclusion is an input. -/
theorem kernel_eq_K [Nontrivial V] :
    (representation ρ).ker = K.subgroupOf N1 := by
  apply le_antisymm
  · intro g hg
    have hgC : ∀ q : N, q ∈ Q1 → ⁅g.val,q⁆ ∈ K := by
      intro q hq
      let q' : N1 := ⟨q,Q1_le_N1 hq⟩
      have hmem : ⁅g,q'⁆.val ∈ Q1 := by
        exact (Q1.subgroupOf N1).mul_mem
          (Q1_normal_in_N1.conj_mem q' hq g)
          ((Q1.subgroupOf N1).inv_mem hq)
      have hker : ⁅g,q'⁆ ∈ (representation ρ).ker := by
        have hh := (representation ρ).ker.mul_mem hg
          ((representation ρ).normal_ker.conj_mem g⁻¹
            ((representation ρ).ker.inv_mem hg) q')
        simpa only [commutatorElement_def, mul_assoc] using hh
      exact K1_le_K ((on_Q1_kernel_iff ρ hQ ⁅g,q'⁆ hmem).mp hker)
    have hsup := (centralizer_preimage g.val g.prop).mp hgC
    obtain ⟨k,hk,w,hw,he⟩ := Subgroup.mem_sup_of_normal_left.mp hsup
    rcases (mem_zpowers_z1_iff w).mp hw with hw | hw
    · change g.val ∈ K
      have hh : k = g.val := by simpa only [hw, mul_one] using he
      exact hh ▸ hk
    · have he' : g = (⟨k,K_le_N1 hk⟩ : N1) * z := by
        apply Subtype.ext
        change g.val = k * z1N
        simpa only [hw] using he.symm
      have hz : z ∈ (representation ρ).ker := by
        have hh : (⟨k,K_le_N1 hk⟩ : N1) ∈ (representation ρ).ker := K_le_kernel ρ hQ hc hk
        exact ((representation ρ).ker.mul_mem_cancel_left hh).mp (he' ▸ hg)
      exact (z_not_mem_kernel ρ hQ hz).elim
  · exact K_le_kernel ρ hQ hc


include hc in
/-- Descent to the actual local quotient. -/
def quotientRepresentation : Representation ℝ N1Quotient (V ⊗[ℝ] SpinSpace) :=
  QuotientGroup.lift (K.subgroupOf N1) (representation ρ) (K_le_kernel ρ hQ hc)

include hc in
theorem quotientRepresentation_mk (g : N1) :
    quotientRepresentation ρ hQ hc (QuotientGroup.mk' (K.subgroupOf N1) g) =
      representation ρ g := rfl

include hc in
theorem quotientRepresentation_faithful [Nontrivial V] :
    Function.Injective (quotientRepresentation ρ hQ hc) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (kernel_eq_K ρ hQ hc).symm

omit hQ in
/-- The source tensor dimension, when the natural factor has dimension 24. -/
theorem finrank_tensor (hV : Module.finrank ℝ V = 24) :
    Module.finrank ℝ (V ⊗[ℝ] SpinSpace) = 98304 := by
  rw [Module.finrank_tensorProduct, hV, finrank_spinSpace]

end Sporadic.Monster.Construction.TrialitySpin.TensorKernel
