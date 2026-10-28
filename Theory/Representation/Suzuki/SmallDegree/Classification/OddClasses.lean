module

public import Theory.SpecificGroups.Suzuki.PRegularClasses
public import Theory.Representation.Suzuki.SmallDegree.Classification

/-!
# Suzuki tensor exhaustion using the proved odd-order class bound

The concrete Suzuki group has at most `q` odd-order conjugacy classes. Applying
this bound to the modular simple-family count removes the class-count premise
from tensor exhaustion. Only simplicity and pairwise inequivalence of the
actual Frobenius tensors remain as independent representation inputs.

Sources: GLS3, §§2.8.2--2.8.8 and the torus normalizers of Theorem 6.5.4.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
universe u

variable {m : ℕ} {K : Type u} [Field K] [Algebra (F m) K]
  [IsAlgClosed K] [CharP K 2]

/-- The proved bound on actual odd-order classes supplies the class-count input
to exhaustion by the concrete simple, pairwise distinct tensors. -/
theorem exists_tensorRep_equiv_of_simple_distinct (hm : 1 ≤ m)
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃ I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) :=
  exists_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist
    (suzuki_odd_conjClasses_card_le m hm) τ hτ

/-- Tensor exhaustion gives a unique support under the two independent
representation inputs; no class-count premise remains. -/
theorem existsUnique_tensorRep_equiv_of_simple_distinct (hm : 1 ≤ m)
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ) :
    ∃! I : Support m, Nonempty (τ.Equiv (tensorRep m K I)) :=
  existsUnique_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist
    (suzuki_odd_conjClasses_card_le m hm) τ hτ

/-- For a faithful irreducible the support is nonempty, with the class-count
premise discharged on the literal Suzuki matrix group. -/
theorem exists_nonempty_tensorRep_equiv_of_simple_distinct (hm : 1 ≤ m)
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m K I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m K I).Equiv (tensorRep m K J)) → I = J)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K (SuzukiMatrixGroup m) V) (hτ : IsIrreducible τ)
    (hfaith : Function.Injective τ) :
    ∃ I : Support m, I.Nonempty ∧ Nonempty (τ.Equiv (tensorRep m K I)) :=
  exists_nonempty_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist
    (suzuki_odd_conjClasses_card_le m hm) τ hτ hfaith

end Representation.SuzukiSmallDegree
