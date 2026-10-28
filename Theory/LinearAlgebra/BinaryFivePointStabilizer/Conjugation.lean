module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Faithful conjugation on the binary displacement kernel

The displacement kernel of a nonzero-vector stabilizer is self-centralizing.
An element commuting with every shear fixes every linear functional on the
quotient by the marked line, hence acts trivially on that quotient. Thus
conjugation on the actual translation group has exactly that group as kernel.

This supplies the faithful action on Q/F in Aschbacher--Smith, Lemma 14.2.21,
printed p.989, when Q/F has been identified with these translations.
-/

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer
open Subgroup

/-- Commuting with all translations forces trivial action modulo the fixed line. -/
public theorem centralizer_kernel_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (z : E) (hz : z ≠ 0) :
    centralizer (kernel z : Set (stabilizer z)) ≤ kernel z := by
  intro g hg
  apply (mem_kernel_iff z g).mpr
  intro x
  apply (Submodule.Quotient.mk_eq_zero (line z)).mp
  by_contra hne
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hne
  let w : line z := ⟨z, Submodule.mem_span_singleton_self z⟩
  let t := kernelShear z (f.smulRight w)
  have hc := congrArg (fun a : stabilizer z => a.val x) (hg t.val t.property)
  change t.val.val (g.val x) = g.val (t.val.val x) at hc
  simp only [t, kernelShear_apply, map_add] at hc
  rw [fixes_line z g _ (f.smulRight w ((line z).mkQ x)).property] at hc
  have he := add_left_cancel hc
  change f ((line z).mkQ (g.val x)) • z = f ((line z).mkQ x) • z at he
  have hs : f ((line z).mkQ (g.val x - x)) • z = 0 := by
    rw [map_sub, map_sub, sub_smul, he, sub_self]
  change f ((line z).mkQ (g.val x - x)) = 1 at hf
  rw [hf, one_smul] at hs
  exact hz hs

/-- The action on translations is faithful modulo translations themselves. -/
public theorem conjugation_kernel {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (z : E) (hz : z ≠ 0) :
    (MulAut.conjNormal : stabilizer z →* MulAut (kernel z)).ker = kernel z := by
  apply le_antisymm
  · intro g hg
    apply centralizer_kernel_le z hz
    intro t ht
    have he := congrArg (fun a : MulAut (kernel z) => (a ⟨t, ht⟩ : stabilizer z))
      (MonoidHom.mem_ker.mp hg)
    change g * t * g⁻¹ = t at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro t
    apply Subtype.ext
    change g * (t : stabilizer z) * g⁻¹ = t
    rw [((kernel z).le_centralizer hg t t.property).symm, mul_inv_cancel_right]

end Theory.LinearAlgebra.BinaryFivePointStabilizer
