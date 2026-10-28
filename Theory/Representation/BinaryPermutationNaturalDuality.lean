module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Self-duality of the binary natural permutation section

The coordinate dot product on the augmentation kernel has constant radical.
It descends to the natural section and is nondegenerate: testing against the
weight-two vectors forces a vector in its radical to be constant. Its invariance
under every coordinate permutation identifies the natural action with its
contragredient. This supplies the dual coefficient module in the covering
formula of Aschbacher–Smith I.1.5 (printed p.408), for the modules in §B.3.
-/

public section

open Module
namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

private def corePairing : core Ω →ₗ[ZMod 2] core Ω →ₗ[ZMod 2] ZMod 2 :=
  (dotProductEquiv (ZMod 2) Ω).toLinearMap.compl₁₂ (core Ω).subtype (core Ω).subtype

private lemma corePairing_apply (v w : core Ω) :
    corePairing Ω v w = ∑ i, v.val i * w.val i := rfl

omit [DecidableEq Ω] in
private lemma coreToNatural_ker (v : core Ω) :
    v ∈ (coreToNatural Ω).ker ↔ v.val ∈ constants Ω := by
  change coreToNatural Ω v = 0 ↔ _
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

private lemma pairing_radical : (coreToNatural Ω).ker ≤ (corePairing Ω).ker := by
  intro v hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((coreToNatural_ker Ω v).mp hv)
  apply LinearMap.ext
  intro w
  change (∑ i, v.val i * w.val i) = 0
  rw [← hc]
  simp only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, ← Finset.mul_sum]
  rw [show ∑ i, w.val i = 0 from w.property, mul_zero]

private lemma pairing_flip_radical : (coreToNatural Ω).ker ≤ (corePairing Ω).flip.ker := by
  intro v hv
  apply LinearMap.ext
  intro w
  have h := LinearMap.congr_fun (pairing_radical Ω hv) w
  simpa only [LinearMap.flip_apply, corePairing_apply, mul_comm] using h

/-- The coordinate dot product descended to the natural section. -/
noncomputable def naturalPairing : natural Ω →ₗ[ZMod 2] natural Ω →ₗ[ZMod 2] ZMod 2 :=
  let E := (coreToNatural Ω).quotKerEquivOfSurjective coreToNatural_surjective
  ((corePairing Ω).liftQ₂ _ _ (pairing_radical Ω) (pairing_flip_radical Ω)).compl₁₂
    E.symm.toLinearMap E.symm.toLinearMap

/-- The descended form is computed using any augmentation representatives. -/
lemma naturalPairing_apply_core (v w : core Ω) :
    naturalPairing Ω (coreToNatural Ω v) (coreToNatural Ω w) =
      ∑ i, v.val i * w.val i := by
  simp [naturalPairing, corePairing_apply]

/-- Weight-two test vectors detect the radical of the descended form. -/
lemma naturalPairing_injective [Nonempty Ω] : Function.Injective (naturalPairing Ω) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨u, rfl⟩ := coreToNatural_surjective v
  have hu (w : core Ω) : (∑ i, u.val i * w.val i) = 0 := by
    have h := LinearMap.congr_fun hv (coreToNatural Ω w)
    simpa only [naturalPairing_apply_core, LinearMap.zero_apply] using h
  let a : Ω := Classical.choice inferInstance
  have hconst (i : Ω) : u.val i = u.val a := by
    let w : core Ω := ⟨Pi.single i 1 + Pi.single a 1, by
      simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
    have h := hu w
    change dotProduct u.val (Pi.single i 1 + Pi.single a 1) = 0 at h
    simp only [dotProduct_add, dotProduct_single, mul_one] at h
    simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left h)
  apply (coreToNatural_ker Ω u).mpr
  exact Submodule.mem_span_singleton.mpr ⟨u.val a, funext fun i => by
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one] using (hconst i).symm⟩

/-- The natural binary permutation section is self-dual. -/
noncomputable def naturalDualEquiv [Nonempty Ω] :
    natural Ω ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (natural Ω) :=
  LinearEquiv.ofBijective (naturalPairing Ω) ⟨naturalPairing_injective Ω,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp
      (naturalPairing_injective Ω)⟩

/-- Self-duality intertwines the full symmetric group action. -/
lemma naturalDualEquiv_equivariant [Nonempty Ω] (g : Equiv.Perm Ω) (v : natural Ω) :
    naturalDualEquiv Ω (naturalRepresentation Ω g v) =
      (naturalRepresentation Ω).dual g (naturalDualEquiv Ω v) := by
  apply LinearMap.ext
  intro w
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  obtain ⟨b, rfl⟩ := coreToNatural_surjective w
  change naturalPairing Ω (naturalRepresentation Ω g (coreToNatural Ω a))
    (coreToNatural Ω b) = naturalPairing Ω (coreToNatural Ω a)
      (naturalRepresentation Ω g⁻¹ (coreToNatural Ω b))
  rw [← coreToNatural_equivariant, ← coreToNatural_equivariant,
    naturalPairing_apply_core, naturalPairing_apply_core]
  change (∑ i, a.val (g.symm i) * b.val i) = ∑ i, a.val i * b.val (g i)
  simpa using Equiv.sum_comp g.symm (fun i => a.val i * b.val (g i))
end BinaryPermutation
