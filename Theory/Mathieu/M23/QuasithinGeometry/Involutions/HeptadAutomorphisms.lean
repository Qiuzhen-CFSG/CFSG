module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Generators
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!+# Automorphisms fixing an M23 involution preserve its heptad stabilizer

The pointwise kernel of the fixed heptad is exactly the two-core of the
involution centralizer, viewed inside the concrete M23 group. For the certified
representative, a product of two centralizer generators acts transitively on
the seven heptad points. The two-core has a fixed point because seven is odd;
normality and transitivity then make it fix every heptad point. Conversely,
the abelian binary translation kernel contains the involution, centralizes it,
and is a normal two-subgroup of its centralizer. Involution fusion transports
this identity to every involution.

The heptad stabilizer is the normalizer of this kernel. Its intrinsic
description therefore proves invariance under every automorphism fixing the
involution, without assumptions on how the automorphism acts on the design.

This supplies the model normalization step for Aschbacher–Smith 2.3.9(7)(f),
printed pp.525–526, using the inner-involution case of 1.1.5(3)(f), printed
p.502, in the combined manuscript of 1 March 2004. The certified generators
and binary kernel are developed in Representative.Generators and
HeptadStructure.BinaryKernel.
-/

public section

open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

private noncomputable abbrev C := centralizer ({involutionRepresentative} : Set M23)

private noncomputable def sevenCycle : C :=
  involutionCentralizerGenerator 6 * involutionCentralizerGenerator 4

private theorem sevenCycle_transitive (a b : Fin 23) (ha : a ∈ omega) (hb : b ∈ omega) :
    ∃ n : Fin 7, (((sevenCycle ^ n.val : C) : M23) : Equiv.Perm (Fin 23)) a = b := by
  have h : ∀ a b : Fin 23, a ∈ omega → b ∈ omega →
      ∃ n : Fin 7, (((sevenCycle ^ n.val : C) : M23) : Equiv.Perm (Fin 23)) a = b := by
    decide +kernel
  exact h a b ha hb

private noncomputable def centralizerAction : C →* Equiv.Perm omega :=
  (setAction omega).comp (Subgroup.inclusion (by
    simpa only [fixedHeptad_involutionRepresentative, involutionHeptad, omega] using
      centralizer_le_fixedHeptad_stabilizer involutionRepresentative))

private theorem core_le_kernel : C.pCoreIn 2 ≤ heptadKernelAmbient := by
  let : MulAction C omega := MulAction.compHom omega centralizerAction
  have hcard : Nat.card omega = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, omega_card]
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := C)).nonempty_fixed_point_of_prime_not_dvd_card
    omega (by rw [hcard]; decide)
  rintro g ⟨u, hu, rfl⟩
  apply (mem_heptadKernelAmbient _).mpr
  intro b hb
  obtain ⟨n, hn⟩ := sevenCycle_transitive a.val b a.property hb
  have hf := smul_mem_fixedPoints_of_normal (sevenCycle ^ n.val) ha
  have he := congrArg Subtype.val (hf ⟨u, hu⟩)
  change (u : M23) • ((((sevenCycle ^ n.val : C) : M23) : Equiv.Perm (Fin 23)) a.val) =
    (((sevenCycle ^ n.val : C) : M23) : Equiv.Perm (Fin 23)) a.val at he
  rwa [hn] at he

private theorem kernel_le_centralizer : heptadKernelAmbient ≤ C := by
  have ht : involutionRepresentative ∈ heptadKernelAmbient := by
    apply (mem_heptadKernelAmbient _).mpr
    intro a ha
    exact (involutionRepresentative_fixed_iff a).mpr ha
  obtain ⟨t, ht, he⟩ := ht
  rintro g ⟨u, hu, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [← he]
  exact congrArg (fun v : heptadKernel => ((v : heptadStabilizer) : M23))
    (heptadKernel_mul_comm ⟨u, hu⟩ ⟨t, ht⟩)

private theorem representative_core_eq_kernel : C.pCoreIn 2 = heptadKernelAmbient := by
  apply le_antisymm core_le_kernel
  apply le_pCoreIn_of_normalizes
    (heptadKernel_isTwoGroup.map heptadStabilizer.subtype) kernel_le_centralizer
  change C ≤ normalizer (heptadKernelAmbient : Set M23)
  rw [heptadKernelAmbient_normalizer]
  simpa only [fixedHeptad_involutionRepresentative, involutionHeptad, heptadStabilizer, omega] using
    centralizer_le_fixedHeptad_stabilizer involutionRepresentative

private theorem centralizer_map (e : MulAut M23) (t : M23) :
    (centralizer ({t} : Set M23)).map e.toMonoidHom = centralizer ({e t} : Set M23) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  rw [← e.injective.eq_iff]
  simp only [map_mul, MulEquiv.apply_symm_apply]

/-- The intrinsic two-core of an involution centralizer, included in M23, is
exactly the pointwise kernel of its fixed heptad. -/
theorem fixedHeptad_centralizer_core_eq {t : M23} (ht : orderOf t = 2) :
    (centralizer ({t} : Set M23)).pCoreIn 2 = heptadPointwiseKernel (fixedHeptad t) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (involutions_isConj involutionRepresentative t involutionRepresentative_order ht)
  have hg' : MulAut.conj g involutionRepresentative = t := hg
  rw [← hg', fixedHeptad_conj, heptadPointwiseKernel_smul,
    fixedHeptad_involutionRepresentative]
  have he : involutionHeptad = omega := by rfl
  rw [he, heptadPointwiseKernel_omega, ← representative_core_eq_kernel,
    map_pCoreIn_of_injective 2 C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    centralizer_map]

/-- Every abstract automorphism fixing an involution preserves the stabilizer
of its actual fixed-point heptad in the natural M23 action. -/
theorem fixedHeptad_stabilizer_map_of_aut_fix {t : M23} (ht : orderOf t = 2)
    (α : MulAut M23) (hα : α t = t) :
    (MulAction.stabilizer M23 (fixedHeptad t)).map α.toMonoidHom =
      MulAction.stabilizer M23 (fixedHeptad t) := by
  rw [← heptadPointwiseKernel_normalizer (fixedHeptad_mem ht),
    map_equiv_normalizer_eq, ← fixedHeptad_centralizer_core_eq ht,
    map_pCoreIn_of_injective 2 _ α.toMonoidHom α.injective,
    centralizer_map, hα]

end Sporadic.Mathieu.M23Geometry

end
