module

public import Theory.Representation.Suzuki.SmallDegree.Models

/-!
# Empty Suzuki tensors and faithful support

The tensor indexed by the empty support is the coefficient-field line with
trivial action. A nonidentity central root matrix therefore forces any tensor
equivalent to a faithful representation to have nonempty support. Equivalences
also preserve support cardinality by the already proved dimension formula.

These facts supply the empty case and the faithful consumer of the Suzuki
absolute classification. They do not assume simplicity of the group or tensor
exhaustion. Sources: GLS3, 2.8.6(b); Guralnick--Malle, *Classification of
2F-modules, II*, §3.1 and Lemma 8.3.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
variable (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]

set_option backward.isDefEq.respectTransparency false in
/-- The empty tensor is the actual trivial coefficient-field line. -/
def emptyTensorEquiv : (tensorRep m K ∅).Equiv
    (Representation.trivial K (SuzukiMatrixGroup m) K) := by
  change (extendScalars K (wordRep m (exponents (∅ : Support m)))).Equiv
    (Representation.trivial K (SuzukiMatrixGroup m) K)
  rw [show exponents (∅ : Support m) = [] by simp [exponents]]
  exact .mk (TensorProduct.AlgebraTensorModule.rid (F m) K K) (by intro g; ext; rfl)

@[simp] theorem tensorRep_empty_apply (g : SuzukiMatrixGroup m)
    (v : TensorSpace m K ∅) : tensorRep m K ∅ g v = v := by
  apply (emptyTensorEquiv m K).toLinearEquiv.injective
  exact LinearMap.congr_fun ((emptyTensorEquiv m K).isIntertwining' g) v

/-- The empty support is irreducible over every extension field. -/
theorem tensorRep_empty_irreducible : IsIrreducible (tensorRep m K ∅) := by
  have ht : IsIrreducible (Representation.trivial K (SuzukiMatrixGroup m) K) := by
    constructor
    intro S
    rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  exact (RepEquiv.irreducible_euqiv
    (RepEquiv.ofRepresentationEquiv (emptyTensorEquiv m K))).mpr ht

variable {m K}

/-- Genuine tensor equivalence preserves the number of selected positions. -/
theorem support_card_eq_of_tensorRep_equiv {I J : Support m}
    (e : (tensorRep m K I).Equiv (tensorRep m K J)) : I.card = J.card := by
  have h := e.toLinearEquiv.finrank_eq
  rw [finrank_tensorSpace, finrank_tensorSpace] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 4) h

/-- A faithful representation cannot be the empty tensor. This uses a literal
nonidentity central root matrix, so no simplicity or order formula is needed. -/
theorem support_nonempty_of_faithful_equiv
    {V : Type*} [AddCommGroup V] [Module K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : Function.Injective τ)
    {I : Support m} (e : τ.Equiv (tensorRep m K I)) : I.Nonempty := by
  by_contra hI
  have hI : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
  subst I
  let g : SuzukiMatrixGroup m :=
    ⟨SuzukiRootGL m 0 1, Subgroup.subset_closure (Or.inl ⟨0, 1, rfl⟩)⟩
  have hg : g ≠ 1 := by
    intro he
    have hc := congrArg (fun x : SuzukiMatrixGroup m => x.val.val 0 2) he
    simp [g, SuzukiRootGL, SuzukiRootMatrix] at hc
  apply hg
  apply hτ
  ext v
  apply e.toLinearEquiv.injective
  calc
    e (τ g v) = tensorRep m K ∅ g (e v) := LinearMap.congr_fun (e.isIntertwining' g) v
    _ = e v := tensorRep_empty_apply m K g (e v)
    _ = e (τ 1 v) := by simp

end Representation.SuzukiSmallDegree
