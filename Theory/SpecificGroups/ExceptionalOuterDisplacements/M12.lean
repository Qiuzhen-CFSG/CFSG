module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.GroupTheory.DoubleCoverCentralizer.DisplacementTransport

/-!
# A non-two-central displacement for the standard outer involution of M₁₂

The actual degree-24 generator A induces an outer involution τ on the original
Witt-design M₁₂. For the original degree-12 generators a and b, the word
x = (ba)³b has displacement x τ(x)⁻¹ = (0 1)(2 5)(3 10)(4 11)(6 7)(8 9).
The marked embedding and block restriction reduce this identity to a small
permutation calculation checked by Lean's kernel.

The displacement moves all twelve points. By Sylow conjugacy and the known
center {1,z} of the marked Sylow subgroup, every two-central element moves
either zero or eight points. This rules out centrality in every Sylow
two-subgroup. Transport gives the same conclusion for every automorphism
conjugate to τ; exhaustive outer-involution coverage is a separate result.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2,
observation (iii), printed p.411 / PDF p.422. The permutation generators and
block conventions are those of ATLAS M12d2G1-p24B0, as attributed in
Theory/Mathieu/M12/ExceptionalParabolics/Extension/Seeds.lean.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension
open Subgroup M12SmallPair Theory.GroupTheory.DoubleCoverCentralizer
set_option maxRecDepth 10000

/-- The literal first generator of the fixed degree-24 outer extension. -/
@[expose] def outerA : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩

/-- The standard outer action, with the fixed automorphism-model normalization. -/
@[expose] noncomputable def outerInvolution : MulAut M12 := automorphismEquiv outerA

/-- The actual extension representative has order two. -/
theorem outerA_order : orderOf outerA = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The representative moves the marked block and so lies outside the inner subgroup. -/
theorem outerA_not_mem_inner : outerA ∉ inner := by
  intro h
  have he := blockRestriction_spec ⟨outerA, h⟩ 0
  have hn : ∀ i : Fin 12, generatorA (blockLabel 0) ≠ blockLabel i := by decide +kernel
  exact hn _ he

theorem outerInvolution_order : orderOf outerInvolution = 2 :=
  (automorphismEquiv.orderOf_eq outerA).trans outerA_order

/-- The normalized action is genuinely outer on the original M₁₂ carrier. -/
theorem outerInvolution_not_inner : ¬ ∃ g : M12, outerInvolution = MulAut.conj g := by
  rintro ⟨g, hg⟩
  have he : outerA = innerModel.embedding g :=
    automorphismEquiv.injective (hg.trans (automorphismEquiv_embedding g).symm)
  apply outerA_not_mem_inner
  rw [he]
  exact (innerModel.equiv g).property

/-- The displacement witness in the original degree-12 Witt-design group. -/
@[expose] noncomputable def displacementWitness : M12 :=
  (originalB * originalA) ^ 3 * originalB

private theorem blockRestriction_innerModel (x : M12) :
    blockRestriction (innerModel.equiv x) = x := by
  let f : M12 →* M12 := blockRestriction.comp innerModel.equiv.toMonoidHom
  have hgen : f.eqLocus (MonoidHom.id M12) = ⊤ := by
    apply original_pair_generates
    · change blockRestriction (innerModel.equiv originalA) = originalA
      rw [show innerModel.equiv originalA = ⟨innerA, subset_closure (by simp)⟩ from
        Subtype.ext innerModel.generatorA_eq]
      exact blockRestriction_innerA
    · change blockRestriction (innerModel.equiv originalB) = originalB
      rw [show innerModel.equiv originalB = ⟨innerB, subset_closure (by simp)⟩ from
        Subtype.ext innerModel.generatorB_eq]
      exact blockRestriction_innerB
  have hx : x ∈ f.eqLocus (MonoidHom.id M12) := hgen ▸ mem_top x
  exact hx

private theorem embedding_block (x : M12) (i : Fin 12) :
    (innerModel.embedding x).val (blockLabel i) = blockLabel (x.val i) := by
  have he := blockRestriction_spec (innerModel.equiv x) i
  rw [blockRestriction_innerModel] at he
  exact he

private def displacementPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1] * List.formPerm [2, 5] * List.formPerm [3, 10] *
    List.formPerm [4, 11] * List.formPerm [6, 7] * List.formPerm [8, 9]

private theorem embedding_outerInvolution (x : M12) :
    innerModel.embedding (outerInvolution x) =
      outerA * innerModel.embedding x * outerA⁻¹ := by
  apply automorphismEquiv.injective
  rw [automorphismEquiv_embedding, map_mul, map_mul, map_inv, automorphismEquiv_embedding]
  change MulAut.conj (outerInvolution x) =
    outerInvolution * MulAut.conj x * outerInvolution⁻¹
  apply MulEquiv.ext
  intro y
  change outerInvolution x * y * (outerInvolution x)⁻¹ =
    outerInvolution (x * (outerInvolution.symm y) * x⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem displacement_perm :
    (displacementWitness * (outerInvolution displacementWitness)⁻¹ : M12).val =
      displacementPerm := by
  apply Equiv.ext
  intro i
  apply blockLabel_injective
  rw [← embedding_block]
  have he : innerModel.embedding (outerInvolution displacementWitness) =
      outerA * innerModel.embedding displacementWitness * outerA⁻¹ :=
    embedding_outerInvolution displacementWitness
  rw [map_mul, map_inv, he]
  simp only [displacementWitness, map_mul, map_pow,
    innerModel.embedding_originalA, innerModel.embedding_originalB]
  have h : ∀ i : Fin 12,
      ((innerB * innerA) ^ 3 * innerB *
        (outerA * ((innerB * innerA) ^ 3 * innerB) * outerA⁻¹)⁻¹).val (blockLabel i) =
        blockLabel (displacementPerm i) := by decide +kernel
  exact h i

/-- The literal displacement of the published witness is an involution. -/
theorem displacementWitness_order :
    orderOf (displacementWitness * (outerInvolution displacementWitness)⁻¹) = 2 := by
  rw [← Subgroup.orderOf_coe, displacement_perm]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The literal displacement is fixed-point-free in the original action. -/
theorem displacementWitness_support :
    ((displacementWitness * (outerInvolution displacementWitness)⁻¹ : M12).val).support.card =
      12 := by
  rw [displacement_perm]
  decide +kernel

private theorem not_twoCentral_of_support_twelve (u : M12)
    (hu : (u : Equiv.Perm (Fin 12)).support.card = 12) : ¬ TwoCentral u := by
  rintro ⟨P, huP, hc⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P commonSylow
  have hv : ∃ h : MulAut.conj g u ∈ (g • P : Sylow 2 M12),
      (⟨MulAut.conj g u, h⟩ : (g • P : Sylow 2 M12)) ∈
        Subgroup.center (g • P : Sylow 2 M12) := by
    refine ⟨(P.equivSMul g ⟨u, huP⟩).property, ?_⟩
    change P.equivSMul g ⟨u, huP⟩ ∈ Subgroup.center (g • P : Sylow 2 M12)
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨v, rfl⟩ := (P.equivSMul g).surjective y
    simpa only [← map_mul] using congrArg (P.equivSMul g)
      (Subgroup.mem_center_iff.mp hc v)
  rw [hg] at hv
  obtain ⟨hv, hcv⟩ := hv
  have hs : ((MulAut.conj g u : M12) : Equiv.Perm (Fin 12)).support.card = 12 := by
    change ((g : Equiv.Perm (Fin 12)) * (u : Equiv.Perm (Fin 12)) *
      (g : Equiv.Perm (Fin 12))⁻¹).support.card = 12
    rw [Equiv.Perm.card_support_conj, hu]
  rcases (sylowCandidate_center_mem ⟨_, hv⟩).mp hcv with he | he
  · change MulAut.conj g u = 1 at he
    rw [he] at hs
    norm_num at hs
  · change MulAut.conj g u = M12SmallPair.z at he
    rw [he] at hs
    have hz : (M12SmallPair.z : Equiv.Perm (Fin 12)).support.card = 8 := by decide +kernel
    omega

/-- No Sylow two-subgroup has the witness's displacement in its center. -/
theorem displacementWitness_not_twoCentral :
    ¬ TwoCentral (displacementWitness * (outerInvolution displacementWitness)⁻¹) :=
  not_twoCentral_of_support_twelve _ displacementWitness_support

/-- Unconditional non-two-central displacement for the fixed standard outer involution. -/
theorem outerInvolution_displacement : HasNonTwoCentralDisplacement outerInvolution :=
  ⟨displacementWitness, displacementWitness_order, displacementWitness_not_twoCentral⟩

/-- The representative calculation transports to any conjugate automorphism.
The outer-involution coverage theorem supplies this premise in source assembly. -/
theorem conjugate_outerInvolution_displacement (r : MulAut M12)
    (hr : IsConj outerInvolution r) : HasNonTwoCentralDisplacement r := by
  obtain ⟨e, he⟩ := isConj_iff.mp hr
  rw [← he]
  exact outerInvolution_displacement.map e

end Sporadic.Mathieu.M12ExceptionalExtension
