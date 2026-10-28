module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.Cyclicity
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct

/-!
# Applying Suzuki tensor cyclicity to irreducibility

The concrete invariant pairing discharges the orbit-span premise in the
existing simplicity criterion for exactly the given tensor representation.
Only uniqueness of the actual root-fixed line remains explicit. Its independent
producer and the unconditional assembly are owned by `SimpleDistinct`.

Sources: GLS3, §§2.8.2–2.8.8; Guralnick–Malle,
*Classification of 2F-modules, II*, §3.1, equation (3.2).
-/

public section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- The pairing removes the orbit-span assumption from the existing tensor
irreducibility criterion, over every coefficient field extension. -/
theorem tensorRep_irreducible_of_fixedLine_pairing {m : ℕ} {K : Type*}
    [Field K] [Algebra (F m) K] (hm : 1 ≤ m) (I : Support m)
    (hfixed : ∀ v : TensorSpace m K I,
      (∀ g ∈ SuzukiRootSubgroup m, tensorRep m K I g v = v) →
        ∃ c : K, v = c • tensorHighestVector m K I) :
    IsIrreducible (tensorRep m K I) := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (F m) K).injective 2
  exact tensorRep_irreducible_of_fixedLine_and_span hm I hfixed
    (tensorHighestVector_orbit_span_of_fixedLine hm I hfixed)

end Representation.SuzukiSmallDegree
end
