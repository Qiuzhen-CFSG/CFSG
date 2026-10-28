module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicTensorDefs
public import Mathlib.Data.List.FinRange

/-!
# Permuting the actual factors of a tensor prefix

Associativity, symmetry, and the trivial one-dimensional factor give an
intertwining equivalence for every permutation of a finite list of actual
representations. Compare the repository's left-associated tensor prefix
with this list construction. The finite Ree application reorders by the
ordinary-index permutation; dimension equality alone would not suffice.

Source: the tensor-product construction in Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
universe u v
variable {F : Type u} [Field F] {G : Type v} [Group G]

private def tensorEquiv {V W X Y : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G X} {π : Representation F G Y}
    (e : Representation.Equiv ρ σ) (f : Representation.Equiv τ π) :
    Representation.Equiv (ρ.tprod τ) (σ.tprod π) :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (e.toIntertwiningMap.tensor f.toIntertwiningMap).2

private def listTensor : List (FDRep F G) → FDRep F G
  | [] => FDRep.of (Representation.trivial F G F)
  | V :: l => FDRep.of (Representation.tprod V.ρ (listTensor l).ρ)

private theorem listTensor_perm {l l' : List (FDRep F G)} (h : l.Perm l') :
    Nonempty (Representation.Equiv (listTensor l).ρ (listTensor l').ρ) := by
  induction h with
  | nil => exact ⟨.refl _⟩
  | cons V _ ih => exact ⟨tensorEquiv (.refl V.ρ) ih.some⟩
  | swap V W l =>
    exact ⟨(Representation.TensorProduct.assoc W.ρ V.ρ (listTensor l).ρ).symm.trans
      ((tensorEquiv (Representation.TensorProduct.comm W.ρ V.ρ) (.refl (listTensor l).ρ)).trans
        (Representation.TensorProduct.assoc V.ρ W.ρ (listTensor l).ρ))⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩

private def appendLast (l : List (FDRep F G)) (V : FDRep F G) :
    Representation.Equiv (Representation.tprod (listTensor l).ρ V.ρ)
      (listTensor (l ++ [V])).ρ := by
  induction l with
  | nil =>
    exact (Representation.TensorProduct.lid F V.ρ).trans
      (Representation.TensorProduct.rid F V.ρ).symm
  | cons W l ih =>
    exact (Representation.TensorProduct.assoc W.ρ (listTensor l).ρ V.ρ).trans
      (tensorEquiv (.refl W.ρ) ih)

private def prefixList (V : ℕ → FDRep F G) (n : ℕ) :
    Representation.Equiv (tensorPrefix V n).ρ (listTensor ((List.range n).map V)).ρ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact (tensorEquiv ih (.refl (V n).ρ)).trans (appendLast _ _)

/-- Permuting a finite list of actual factors gives an equivalence of the
corresponding tensor representations. -/
theorem tensorPrefix_equiv_of_list_perm (V W : ℕ → FDRep F G) (n : ℕ)
    (h : ((List.range n).map V).Perm ((List.range n).map W)) :
    Nonempty (Representation.Equiv (tensorPrefix V n).ρ (tensorPrefix W n).ρ) :=
  ⟨(prefixList V n).trans ((listTensor_perm h).some.trans (prefixList W n).symm)⟩

/-- Pointwise intertwining equivalences tensor on a finite prefix. -/
theorem tensorPrefix_equiv_of_factors (V W : ℕ → FDRep F G) (n : ℕ)
    (h : ∀ i < n, Nonempty (Representation.Equiv (V i).ρ (W i).ρ)) :
    Nonempty (Representation.Equiv (tensorPrefix V n).ρ (tensorPrefix W n).ρ) := by
  induction n with
  | zero => exact ⟨.refl _⟩
  | succ n ih =>
    exact ⟨tensorEquiv (ih fun i hi => h i (Nat.lt_succ_of_lt hi)).some
      (h n (Nat.lt_succ_self n)).some⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
