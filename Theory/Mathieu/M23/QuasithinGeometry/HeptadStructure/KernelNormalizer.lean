module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore

/-!
# Recovering the heptad stabilizer from its pointwise kernel

The binary translation kernel fixes exactly the seven heptad points: a
translation fixing a complementary point is the identity. Its normalizer
therefore preserves the heptad. Conversely the setwise stabilizer normalizes
the kernel of its action. Conjugation transports this equality to every Witt
heptad in the natural action of M23.

This identifies the normalizer needed in the intrinsic automorphism argument
for Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526. The translation action
and its freeness come from HeptadStructure.BinaryKernel.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

theorem mem_omega_iff_heptadKernel_fixed (a : Fin 23) :
    a ∈ omega ↔ ∀ u : heptadKernel, ((u : heptadStabilizer) : M23) • a = a := by
  constructor
  · intro ha u
    exact (mem_heptadKernel u).mp u.property a ha
  · intro ha
    by_contra hn
    have hb : heptadKernel = ⊥ := by
      apply bot_unique
      intro u hu
      have he := heptadKernel_eq_one_of_fix ⟨u, hu⟩ hn (ha ⟨u, hu⟩)
      exact congrArg Subtype.val he
    have hc := heptadKernel_card
    rw [hb, Subgroup.card_bot] at hc
    contradiction

theorem heptadKernelAmbient_normalizer :
    normalizer (heptadKernelAmbient : Set M23) = heptadStabilizer := by
  apply le_antisymm
  · intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    apply (mem_omega_iff_heptadKernel_fixed _).mpr
    intro u
    have hu : ((u : heptadStabilizer) : M23) ∈ heptadKernelAmbient :=
      ⟨u, u.property, rfl⟩
    have hv := (mem_normalizer_iff.mp ((normalizer (heptadKernelAmbient : Set M23)).inv_mem hg)
      ((u : heptadStabilizer) : M23)).mp hu
    have hf := (mem_heptadKernelAmbient _).mp hv a ha
    have he := congrArg (fun b : Fin 23 => g • b) hf
    simpa only [inv_inv, mul_smul, smul_inv_smul] using he
  · have hn : (heptadKernelAmbient.subgroupOf heptadStabilizer).Normal := by
      have he : heptadKernelAmbient.subgroupOf heptadStabilizer = heptadKernel := by
        ext x
        constructor
        · rintro ⟨y, hy, he⟩
          exact (Subtype.ext he : y = x) ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [he]
      infer_instance
    exact (normal_subgroupOf_iff_le_normalizer heptadKernelAmbient_le).mp hn

/-- The pointwise kernel, included into M23, for a specified finite set. -/
noncomputable def heptadPointwiseKernel (B : Finset (Fin 23)) : Subgroup M23 :=
  (setAction B).ker.map (MulAction.stabilizer M23 B).subtype

@[simp] theorem mem_heptadPointwiseKernel (B : Finset (Fin 23)) (g : M23) :
    g ∈ heptadPointwiseKernel B ↔ ∀ a ∈ B, g • a = a :=
  mem_setAction_ker_map B g

@[simp] theorem heptadPointwiseKernel_omega :
    heptadPointwiseKernel omega = heptadKernelAmbient := by
  rw [heptadPointwiseKernel, heptadKernelAmbient, heptadKernel_eq_ker]

theorem heptadPointwiseKernel_smul (g : M23) (B : Finset (Fin 23)) :
    heptadPointwiseKernel (g • B) = (heptadPointwiseKernel B).map (MulAut.conj g).toMonoidHom := by
  ext u
  rw [Subgroup.mem_map_equiv, mem_heptadPointwiseKernel, mem_heptadPointwiseKernel]
  constructor
  · intro hu a ha
    have hga : g • a ∈ g • B := Finset.smul_mem_smul_finset ha
    have he := congrArg (fun b : Fin 23 => g⁻¹ • b) (hu (g • a) hga)
    simpa only [MulAut.conj_symm_apply, mul_smul, inv_smul_smul] using he
  · intro hu a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp ha
    have he := congrArg (fun b : Fin 23 => g • b) (hu b hb)
    simpa only [MulAut.conj_symm_apply, mul_smul, smul_inv_smul] using he

/-- Recover every heptad stabilizer intrinsically from its pointwise kernel. -/
theorem heptadPointwiseKernel_normalizer {B : Finset (Fin 23)} (hB : B ∈ m23Blocks) :
    normalizer (heptadPointwiseKernel B : Set M23) = MulAction.stabilizer M23 B := by
  obtain ⟨g, rfl⟩ := exists_smul_omega_eq hB
  rw [heptadPointwiseKernel_smul, heptadPointwiseKernel_omega,
    ← Subgroup.map_equiv_normalizer_eq, heptadKernelAmbient_normalizer,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]

end Sporadic.Mathieu.M23Geometry

end
