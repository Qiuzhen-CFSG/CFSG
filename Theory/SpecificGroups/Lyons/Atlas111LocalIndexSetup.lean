module

public import Theory.SpecificGroups.Lyons.Atlas111OrderSetup
public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# Interfaces for the concrete Lyons coset certificates

The subgroup is the literal `LyG1-max1W1` subgroup from `Atlas111OrderSetup`.
An upper certificate covers the matrix-generated group by 8835156 right cosets;
a lower certificate separates that many right cosets. Their representative
families need not agree. The results here assemble those certificates, without
assuming the order or simplicity of the ambient group or the order of the
subgroup. Constructing the certificates remains a separate obligation.

Source for the subgroup words: ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
-/

namespace Lyons.OrderCertificate

/-- The ambient generators, indexed for the coset-certificate interface. -/
@[expose] public def indexGenerator : Bool → LyonsGroup
  | false => generatorA
  | true => generatorB

public theorem closure_range_indexGenerator :
    Subgroup.closure (Set.range indexGenerator) = ⊤ := by
  have hr : Set.range indexGenerator = ({generatorA, generatorB} : Set LyonsGroup) := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [indexGenerator]
    · intro hx
      rcases Set.mem_insert_iff.mp hx with h | h
      · exact ⟨false, h.symm⟩
      · exact ⟨true, (Set.mem_singleton_iff.mp h).symm⟩
  rw [hr]
  exact closure_generators

/-- Concrete transitions suffice for the required upper bound. -/
public theorem localIndex_le_of_cover
    (C : Subgroup.GeneratorCosetCover localSubgroup indexGenerator (Fin 8835156)) :
    localSubgroup.index ≤ 8835156 := by
  simpa using C.index_le_card closure_range_indexGenerator

/-- A separate family of distinct right cosets suffices for the lower bound. -/
public theorem le_localIndex_of_separation (r : Fin 8835156 → LyonsGroup)
    (hsep : ∀ i j, r i * (r j)⁻¹ ∈ localSubgroup → i = j) :
    8835156 ≤ localSubgroup.index := by
  simpa using localSubgroup.card_le_index_of_rightCoset_separation r hsep

end Lyons.OrderCertificate
