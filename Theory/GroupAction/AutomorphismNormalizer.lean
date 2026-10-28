module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Automorphisms realized by a permutation normalizer

For a transitive action, an automorphism that takes one point stabilizer to
another induces a permutation of the points. Choose representatives sending
the first base point to each point; equality of stabilizers makes the formula
`g • x ↦ f(g) • y` well defined and bijective. Equivariance then realizes the
automorphism by conjugation in the permutation normalizer.

Consequently, if automorphisms preserve the class of point stabilizers and
the permutation group is self-normalizing, all its automorphisms are inner.
These are separate hypotheses: self-normalization alone controls only the
automorphisms realized in this particular action.

This is an elementary consequence of the orbit–stabilizer description of a
transitive action. The application to the Rudvalis entry of GLS3, Table 5.3r,
retains both concrete hypotheses for separate proof.
-/

public section

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]

/-- Transport of one stabilizer realizes an automorphism on a transitive set. -/
theorem exists_perm_of_stabilizer_map_eq (f : MulAut G) (x y : X)
    (hf : (stabilizer G x).map f.toMonoidHom = stabilizer G y) :
    ∃ σ : Equiv.Perm X, σ x = y ∧ ∀ (g : G) (z : X), σ (g • z) = f g • σ z := by
  classical
  choose r hr using fun z : X => exists_smul_eq G x z
  have hmem (g : G) : g • x = x ↔ f g • y = y := by
    change g ∈ stabilizer G x ↔ f g ∈ stabilizer G y
    rw [← hf]
    exact (Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective).symm
  have heq (g h : G) : g • x = h • x ↔ f g • y = f h • y := by
    rw [← inv_smul_eq_iff, ← mul_smul, hmem]
    simp only [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
  let s : X → X := fun z => f (r z) • y
  have hs (g : G) : s (g • x) = f g • y :=
    (heq (r (g • x)) g).mp (hr (g • x))
  have hsi : Function.Injective s := by
    intro z w hzw
    exact (hr z).symm.trans (((heq (r z) (r w)).mpr hzw).trans (hr w))
  have hss : Function.Surjective s := by
    intro z
    obtain ⟨g, hg⟩ := exists_smul_eq G y z
    refine ⟨f.symm g • x, ?_⟩
    rw [hs, f.apply_symm_apply, hg]
  refine ⟨Equiv.ofBijective s ⟨hsi, hss⟩, ?_, ?_⟩
  · change s x = y
    simpa using hs 1
  · intro g z
    change s (g • z) = f g • s z
    rw [← hr z, ← mul_smul, hs, map_mul, mul_smul, hs]

end MulAction

namespace Subgroup

variable {X : Type*} (P : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive P X]

/-- An automorphism transporting a point stabilizer comes from the permutation normalizer. -/
theorem exists_normalizer_of_stabilizer_map_eq (f : MulAut P) (x y : X)
    (hf : (MulAction.stabilizer P x).map f.toMonoidHom = MulAction.stabilizer P y) :
    ∃ σ : normalizer (P : Set (Equiv.Perm X)), P.normalizerMonoidHom σ = f := by
  obtain ⟨σ, _, hσ⟩ := MulAction.exists_perm_of_stabilizer_map_eq f x y hf
  have hconj (g : P) : σ * g.val * σ⁻¹ = (f g).val := by
    ext z
    change σ (g • (σ⁻¹ z)) = f g • z
    rw [hσ]
    simp
  have hn : σ ∈ normalizer (P : Set (Equiv.Perm X)) := by
    intro g
    constructor
    · intro hg
      rw [hconj ⟨g, hg⟩]
      exact (f ⟨g, hg⟩).property
    · intro hg
      let k : P := ⟨σ * g * σ⁻¹, hg⟩
      have hk := hconj (f.symm k)
      rw [f.apply_symm_apply] at hk
      have he : (f.symm k).val = g := by
        apply mul_right_cancel (b := σ⁻¹)
        apply mul_left_cancel (a := σ)
        exact hk
      rw [← he]
      exact (f.symm k).property
  refine ⟨⟨σ, hn⟩, ?_⟩
  apply MulEquiv.ext
  intro g
  exact Subtype.ext (hconj g)

/-- Class invariance of point stabilizers and self-normalization force every
abstract automorphism to be inner. -/
theorem conj_surjective_of_stabilizers_of_normalizer (x : X)
    (hf : ∀ f : MulAut P, ∃ y : X,
      (MulAction.stabilizer P x).map f.toMonoidHom = MulAction.stabilizer P y)
    (hn : normalizer (P : Set (Equiv.Perm X)) = P) :
    Function.Surjective (MulAut.conj : P →* MulAut P) := by
  intro f
  obtain ⟨y, hy⟩ := hf f
  obtain ⟨σ, hσ⟩ := exists_normalizer_of_stabilizer_map_eq P f x y hy
  have hmem : σ.val ∈ P := le_of_eq hn σ.property
  refine ⟨⟨σ.val, hmem⟩, ?_⟩
  rw [← hσ]
  rfl

end Subgroup
