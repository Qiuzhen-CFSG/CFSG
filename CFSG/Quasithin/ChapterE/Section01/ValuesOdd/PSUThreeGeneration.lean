module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors

/-!
# Odd-prime PSU₃ upper generation: model transport and remaining branches

The source is E.1.14(7), printed p.214 of Aschbacher--Smith, with the prime
parameter specified in A.2.3(2), printed p.33. The original model has an
arbitrary nondegenerate Hermitian form over a field of order p² and an actual
equivalence to the image of SU₃ in PGL. `ModelInputs` proves normalization
and nonabelianness without changing that model, including at p = 3.
`InnerActors` reduces every remaining inner actor to a genuine four-group
and checks the quotient-rank clause when a local radical contains one of
its involutions.

The assembly below discharges the nonabelian model input to the shared
simple-socle construction and separates the remaining large-family cases.
It is conditional: neither the simple-socle E₂ construction nor the two
large-family exclusions is claimed here. The final source theorem must
supply all three, including the outer two-extensions, before the upper
bound is established. No value theorem is exported by this partial assembly.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The concrete PSU₃ consumer of the component construction and the two
independent large-family exclusions. All unfinished inputs remain explicit. -/
theorem isEGenerated_of_model_and_local_cases
    (T : Sylow 2 G) [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (hcomponent : ¬ IsMulCommutative (generalizedFitting G) →
      ∀ A : Subgroup G, IsElementaryAbelian 2 A →
        A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hinner : ∀ d : LargeFamilyObstruction T,
      (∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ generalizedFitting G) → False)
    (houter : ∀ d : LargeFamilyObstruction T,
      (∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ →
        ¬ A ≤ generalizedFitting G) → False) : IsEGenerated 1 G :=
  isEGenerated_of_large_family_cases (generalizedFitting G) T
    (hcomponent (nonabelian_of_model hp hodd hmodel)) hinner houter

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
