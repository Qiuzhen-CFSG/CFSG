module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.Data.Fintype.Perm

/-!
# Recognition of the natural binary S₃-plane

A transposition fixes a nonzero vector in characteristic two. Its three
translates define an equivariant map from the three-point permutation module.
The map is nonzero on the even-weight core: otherwise the original vector
would be fixed by all of S₃, contradicting irreducibility in dimension two.
The core map is therefore surjective, and dimensions make it an equivalence.

This supplies the natural-action step for Aschbacher–Smith, combined
manuscript (1 March 2004), proof of 13.8.6(4), printed p.948.
-/

public section

open Representation Module Subgroup
open scoped BigOperators

namespace Representation.BinaryPlaneRecognition
local notation "S3" => Equiv.Perm (Fin 3)
private def t : S3 := Equiv.swap 1 2
private def rep (i : Fin 3) : S3 := Equiv.swap 0 i

private lemma stabilizer (g : S3) (hg : g 0 = 0) : g = 1 ∨ g = t := by
  revert g; decide +kernel

private lemma rep_zero (i : Fin 3) : rep i 0 = i := by
  simp [rep]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma binary_neg (v : V) : -v = v := by
  have h := @two_smul (ZMod 2) V _ _ _ v
  have hh : v + v = 0 := by
    simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using h.symm
  exact (eq_neg_iff_add_eq_zero.mpr hh).symm

private lemma fixed_seed (σ : Representation (ZMod 2) S3 V) [Nontrivial V] :
    ∃ w : V, w ≠ 0 ∧ σ t w = w := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  by_cases hfix : σ t v = v
  · exact ⟨v, hv, hfix⟩
  refine ⟨σ t v - v, sub_ne_zero.mpr hfix, ?_⟩
  have ht : t * t = 1 := by decide +kernel
  rw [map_sub, ← Module.End.mul_apply, ← map_mul, ht, map_one,
    Module.End.one_apply]
  simp only [sub_eq_add_neg, binary_neg, add_comm]

private lemma orbit_equivariant (σ : Representation (ZMod 2) S3 V)
    (w : V) (hw : σ t w = w) (g : S3) (i : Fin 3) :
    σ g (σ (rep i) w) = σ (rep (g i)) w := by
  have h0 : (rep (g i))⁻¹ * g * rep i ∈ (MulAction.stabilizer S3 (0 : Fin 3)) := by
    change ((rep (g i))⁻¹ * g * rep i) 0 = 0
    simp only [Equiv.Perm.mul_apply, rep_zero]
    exact ((rep (g i)).symm_apply_eq.mpr (rep_zero (g i)).symm)
  have hf : σ ((rep (g i))⁻¹ * g * rep i) w = w := by
    rcases stabilizer _ h0 with h | h
    · rw [h, map_one]; rfl
    · rw [h, hw]
  have he := congrArg (σ (rep (g i))) hf
  simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc,
    mul_inv_cancel_left] using he

private def orbitMap (σ : Representation (ZMod 2) S3 V)
    (w : V) (hw : σ t w = w) :
    IntertwiningMap (BinaryPermutation.representation (Fin 3)) σ where
  toLinearMap :=
    { toFun := fun v => ∑ i, v i • σ (rep i) w
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c v; simp [Finset.smul_sum, smul_smul] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change (∑ i, v (g.symm i) • σ (rep i) w) = σ g (∑ i, v i • σ (rep i) w)
    simp only [map_sum, map_smul, orbit_equivariant σ w hw]
    exact (Equiv.sum_comp g (fun i => v (g.symm i) • σ (rep i) w)).symm.trans
      (by simp)

private def coreMap (σ : Representation (ZMod 2) S3 V)
    (w : V) (hw : σ t w = w) :
    IntertwiningMap (BinaryPermutation.coreRepresentation (Fin 3)) σ where
  toLinearMap := (orbitMap σ w hw).toLinearMap.comp (BinaryPermutation.core (Fin 3)).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact IntertwiningMap.isIntertwining _ _ (orbitMap σ w hw) g v

private lemma no_fixed (σ : Representation (ZMod 2) S3 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 2) (w : V) (hw : w ≠ 0)
    (hfix : ∀ g, σ g w = w) : False := by
  let W : Subrepresentation σ :=
    { toSubmodule := Submodule.span (ZMod 2) {w}
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul, hfix]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)) }
  rcases eq_bot_or_eq_top W with he | he
  · have hm : w ∈ W := Submodule.subset_span (by simp)
    rw [he] at hm
    exact hw hm
  · have hs : Submodule.span (ZMod 2) {w} = ⊤ := congrArg Subrepresentation.toSubmodule he
    have hd1 := (finrank_eq_one_iff_of_nonzero w hw).mpr hs
    omega

private lemma coreMap_ne_zero (σ : Representation (ZMod 2) S3 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 2)
    (w : V) (hw : w ≠ 0) (ht : σ t w = w) : coreMap σ w ht ≠ 0 := by
  intro hz
  have horbit (i : Fin 3) : σ (rep i) w = w := by
    let v : BinaryPermutation.core (Fin 3) :=
      ⟨Pi.single i 1 - Pi.single 0 1, by
        simp [BinaryPermutation.mem_core, Finset.sum_sub_distrib]⟩
    have he := DFunLike.congr_fun hz v
    change (∑ j, (Pi.single i (1 : ZMod 2) - Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod 2) j • σ (rep j) w) = 0 at he
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib] at he
    simp [Pi.single_apply, rep] at he
    change σ (rep i) w - σ (1 : S3) w = 0 at he
    simpa only [map_one, Module.End.one_apply] using sub_eq_zero.mp he
  apply no_fixed σ hd w hw
  intro g
  have he := orbit_equivariant σ w ht g 0
  simpa only [horbit] using he

/-- Every irreducible binary S₃-plane is equivalent to the actual
three-point permutation core, with the specified S₃ action unchanged. -/
theorem equiv_three_core_of_irreducible (σ : Representation (ZMod 2) S3 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 2) :
    Nonempty (σ.Equiv (BinaryPermutation.coreRepresentation (Fin 3))) := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨w, hw, ht⟩ := fixed_seed σ
  let f := coreMap σ w ht
  have hf : f ≠ 0 := coreMap_ne_zero σ hd w hw ht
  have hsurj : Function.Surjective f := by
    rcases eq_bot_or_eq_top f.range with he | he
    · exfalso
      apply hf
      ext v
      have hm : f v ∈ f.range := ⟨v, rfl⟩
      rw [he] at hm
      exact hm
    · exact LinearMap.range_eq_top.mp (congrArg Subrepresentation.toSubmodule he)
  have hdim : Module.finrank (ZMod 2) (BinaryPermutation.core (Fin 3)) =
      Module.finrank (ZMod 2) V := by rw [BinaryPermutation.finrank_core, hd]; rfl
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact ⟨(f.ofBijective ⟨hinj, hsurj⟩).symm⟩
end Representation.BinaryPlaneRecognition
