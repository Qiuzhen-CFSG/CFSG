module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# The unitary Borel action in 13.8.20

The source fixes `O³(B)O₂(B)/O₂(B)`, where `B = O²(N_D(S))`.
Its pointwise fixation is expressed by displacement into the embedded
`O₂(B)`. All normality is internal to `B`. In particular every inner
actor coming from that two-core fixes this section.

The full special and projective matrix tori are imported as shared
coordinates. Identifying the actual Borel residual and proving the reverse
actor containment are separate mathematical obligations.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {D : Type*} [Group D]

def FixesThreeTorus (B : Subgroup D) (a : MulAut D) : Prop :=
  ∀ x ∈ residualIn 3 B ⊔ B.pCoreIn 2, a x * x⁻¹ ∈ B.pCoreIn 2

theorem inner_twoCore_fixes (B : Subgroup D) (s : D) (hs : s ∈ B.pCoreIn 2) :
    FixesThreeTorus B (MulAut.conj s) := by
  intro x hx
  have hxB : x ∈ B := (sup_le (map_subtype_le _) (pCoreIn_le 2 B)) hx
  obtain ⟨u, hu, rfl⟩ := hs
  let y : B := ⟨x, hxB⟩
  have hm : ⁅u, y⁆ ∈ pCore 2 B :=
    (commutator_le_left (pCore 2 B) (⊤ : Subgroup B))
      (commutator_mem_commutator hu (mem_top y))
  exact ⟨⁅u, y⁆, hm, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
