module

public import Theory.GroupAction.BinaryFixedLineQuotient
public import Mathlib.LinearAlgebra.Projection

/-!
# Extending a binary plane action through a flag

An automorphism of a subgroup of an elementary abelian two-group extends
by the identity on one complement. The extension preserves every subgroup
containing the original subgroup, so it simultaneously preserves all the
retained cuts of a flag above a plane. No adapted basis is an input.

This is the linear extension used for the literal minimal-parabolic action
in Aschbacher–Smith, Lemma 12.8.9(1), printed pp.852–853.
-/

@[expose] public section

open scoped IsMulCommutative
namespace BinaryFlagPlaneAction
variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

noncomputable def extend (A Q : Submodule k E) (h : IsCompl A Q) (a : A ≃ₗ[k] A) :
    E ≃ₗ[k] E :=
  (A.prodEquivOfIsCompl Q h).symm |>.trans
    ((a.prodCongr (LinearEquiv.refl k Q)).trans (A.prodEquivOfIsCompl Q h))

theorem extend_apply (A Q : Submodule k E) (h : IsCompl A Q) (a : A ≃ₗ[k] A) (v : A) :
    extend A Q h a v = a v := by
  simp [extend]

theorem extend_mem_iff (A Q : Submodule k E) (h : IsCompl A Q) (a : A ≃ₗ[k] A)
    (B : Submodule k E) (hAB : A ≤ B) (v : E) :
    extend A Q h a v ∈ B ↔ v ∈ B := by
  let e := A.prodEquivOfIsCompl Q h
  obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
  change e ((a.prodCongr (LinearEquiv.refl k Q)) (e.symm (e (x,y)))) ∈ B ↔ e (x,y) ∈ B
  rw [e.symm_apply_apply]
  change (a x : E) + (y : E) ∈ B ↔ (x : E) + (y : E) ∈ B
  rw [Submodule.add_mem_iff_right B (hAB (a x).property),
    Submodule.add_mem_iff_right B (hAB x.property)]

variable {D : Type*} [Group D] [IsElementaryAbelian 2 D]

def space (A : Subgroup D) : Submodule (ZMod 2) (Additive D) :=
  AddSubgroup.toZModSubmodule 2 A.toAddSubgroup

def coordinates (A : Subgroup D) : Additive A ≃+ space A where
  toFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
  invFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem exists_extension (A : Subgroup D) (a : MulAut A) :
    ∃ b : MulAut D, (∀ v : A, b (v : D) = (a v : D)) ∧
      ∀ B : Subgroup D, A ≤ B → ∀ v : D, b v ∈ B ↔ v ∈ B := by
  let e := coordinates A
  let c := e.symm.trans (a.toAdditive.trans e)
  let a' : space A ≃ₗ[ZMod 2] space A :=
    { c with map_smul' := ZMod.map_smul c }
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (space A)
  let b' := extend (space A) Q hQ a'
  refine ⟨BinaryFixedLine.linearAutEquiv.symm b', ?_, ?_⟩
  · intro v
    have hv := extend_apply (space A) Q hQ a' (e (Additive.ofMul v))
    exact congrArg Additive.toMul hv
  · intro B hB v
    exact extend_mem_iff (space A) Q hQ a' (space B) hB (Additive.ofMul v)
end BinaryFlagPlaneAction
