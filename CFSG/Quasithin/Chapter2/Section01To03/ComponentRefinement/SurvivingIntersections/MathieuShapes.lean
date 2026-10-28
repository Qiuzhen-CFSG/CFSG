module

public import Theory.GroupTheory.AlternatingBySixteen
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension

/-!
# The actual heptad extension in M₂₃

Conjugating the standard heptad to any heptad transports its pointwise
kernel to the pointwise kernel of that heptad. The explicit binary
translation group has order sixteen, and the induced quotient is A₇.
This identifies the kernel and quotient required by the notation A₇/E₁₆
in Aschbacher–Smith 2.3.9(7)(f), printed p.525.

The subgroup equality L ∩ M = a heptad stabilizer is a separate local
calculation; this module does not assume it follows from the group order.
The underlying permutation and split-extension constructions are in
Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The pointwise fixer of any heptad is E₁₆, with alternating quotient A₇. -/
theorem mathieuTwentyThree_heptad_pointwise_extension {B : Finset (Fin 23)} (hB : B ∈ m23Blocks) :
    IsElementaryAbelian 2 (setAction B).ker ∧
    Nat.card (setAction B).ker = 16 ∧
    Nonempty (((MulAction.stabilizer M23 B) ⧸ (setAction B).ker) ≃*
      alternatingGroup (Fin 7)) := by
  obtain ⟨g, hg⟩ := exists_smul_omega_eq hB
  let e : heptadStabilizer ≃* MulAction.stabilizer M23 B :=
    MulAction.stabilizerEquivStabilizer hg.symm
  have hmap : heptadKernel.map e.toMonoidHom = (setAction B).ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply (mem_setAction_ker B _).mpr
      intro b hb
      have hb' : b ∈ g • omega := hg.symm ▸ hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hb'
      have hfix := (mem_heptadKernel y).mp hy a ha
      change (MulAut.conj g (y : M23)) • (g • a) = g • a
      simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hfix]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply (mem_heptadKernel _).mpr
      intro a ha
      have hfix := (mem_setAction_ker B x).mp hx (g • a)
        (hg ▸ Finset.smul_mem_smul_finset ha)
      change (MulAut.conj g⁻¹ (x : M23)) • a = a
      simp only [MulAut.conj_apply, mul_smul, inv_inv, hfix, inv_smul_smul]
  have he : IsElementaryAbelian 2 heptadKernel := {
    is_comm := ⟨heptadKernel_mul_comm⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr heptadKernel_sq }
  let := he
  have hem : IsElementaryAbelian 2 (heptadKernel.map e.toMonoidHom) :=
    IsElementaryAbelian.map e.toMonoidHom
  refine ⟨hmap ▸ hem, ?_, ?_⟩
  · rw [← hmap]
    exact (Nat.card_congr (e.subgroupMap heptadKernel).toEquiv).symm.trans heptadKernel_card
  · exact ⟨(QuotientGroup.congr heptadKernel (setAction B).ker e hmap).symm.trans
      heptadQuotientAlternatingEquiv⟩

/-- The source extension shape, with its actual normal pointwise kernel. -/
theorem mathieuTwentyThree_heptad_extension {B : Finset (Fin 23)}
    (hB : B ∈ m23Blocks) :
    AlternatingBySixteen (MulAction.stabilizer M23 B) 7 := by
  obtain ⟨he, hc, eq⟩ := mathieuTwentyThree_heptad_pointwise_extension hB
  exact ⟨(setAction B).ker, inferInstance, he, hc, eq⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
