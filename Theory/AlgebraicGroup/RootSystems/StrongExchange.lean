module

public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-! Strong exchange for simple-reflection words in a root system. -/

namespace Theory.AlgebraicGroup

/-- If appending a simple reflection makes the image of its simple root
negative, the resulting Weyl-group element is obtained by deleting one letter
from the original word. -/
public theorem wordProd_strongExchange
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support) (j : b.support)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) j)) :
    ∃ p : List b.support, ∃ i : b.support, ∃ q : List b.support,
      l = p ++ i :: q ∧
        b.wordProd (p ++ q) = b.wordProd l * b.simpleReflection j := by
  induction l with
  | nil =>
      exfalso
      apply hneg
      simpa using b.isPos_of_mem_support j.property
  | cons k l ih =>
      have hneg' : ¬ b.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (b.wordProd l) j)) := by
        rw [b.wordProd_cons] at hneg
        change ¬ b.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (b.wordProd l) j)) at hneg
        exact hneg
      by_cases hpos : b.IsPos (P.weylGroupToPerm (b.wordProd l) j)
      · have heq : P.weylGroupToPerm (b.wordProd l) j = k :=
          (simpleReflection_unique_positiveRoot P b k.property _).mp ⟨hpos, hneg'⟩
        refine ⟨[], k, l, rfl, ?_⟩
        simp only [List.nil_append, b.wordProd_cons]
        change b.wordProd l = b.simpleReflection k *
          (b.wordProd l * RootPairing.weylGroup.ofIdx P j)
        rw [b.wordProd_mul_ofIdx, ← mul_assoc]
        change b.wordProd l = b.simpleReflection k *
          RootPairing.weylGroup.ofIdx P
            (P.weylGroupToPerm (b.wordProd l) j) * b.wordProd l
        rw [heq]
        change b.wordProd l =
          (b.simpleReflection k * b.simpleReflection k) * b.wordProd l
        simp
      · obtain ⟨p, i, q, hdecomp, hprod⟩ := ih hpos
        refine ⟨k :: p, i, q, ?_, ?_⟩
        · simp only [List.cons_append, List.cons.injEq, true_and]
          exact hdecomp
        · simp only [List.cons_append, b.wordProd_cons]
          rw [hprod]
          simp only [mul_assoc]

end Theory.AlgebraicGroup
