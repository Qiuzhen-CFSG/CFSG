module

public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
# Irreducibility of the standard D4 root pairing

Every arm of the standard D4 Cartan matrix is joined to the central vertex
`1`. The resulting Cartan connectivity proves irreducibility of the actual
coordinate root pairing, supplying the hypothesis for Geck's matrix relations.

Source: the D4 diagram of GLS3 §1.8 and the subsystem construction in §2.6
(`refs/KGroup/GLS3/Chapter1.tex`, `refs/KGroup/GLS3/chapter2.tex`).
-/

public section

namespace Theory.AlgebraicGroup.StandardRootSystem

/-- The standard D4 root pairing is irreducible, by Cartan connectivity. -/
theorem typeD4RootPairing_isIrreducible : (typeDRootPairing 2).IsIrreducible := by
  apply Theory.AlgebraicGroup.isIrreducible_of_cartan_connected _
    (typeDRootPairing_base 2)
  · exact ⟨_, (typeDRootPairing_baseEquiv 2 0).property⟩
  · intro s t
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective s
    obtain ⟨j, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective t
    have hc (k : Fin 4) :
        (typeDRootPairing_base 2).cartanMatrix
          (typeDRootPairing_baseEquiv 2 k) (typeDRootPairing_baseEquiv 2 1) ≠ 0 := by
      rw [typeDRootPairing_base_cartanMatrix]
      fin_cases k <;> decide
    have hc' (k : Fin 4) :
        (typeDRootPairing_base 2).cartanMatrix
          (typeDRootPairing_baseEquiv 2 1) (typeDRootPairing_baseEquiv 2 k) ≠ 0 := by
      rw [typeDRootPairing_base_cartanMatrix]
      fin_cases k <;> decide
    exact Relation.ReflTransGen.trans (b := typeDRootPairing_baseEquiv 2 1)
      (.single (hc i)) (.single (hc' j))

end Theory.AlgebraicGroup.StandardRootSystem
