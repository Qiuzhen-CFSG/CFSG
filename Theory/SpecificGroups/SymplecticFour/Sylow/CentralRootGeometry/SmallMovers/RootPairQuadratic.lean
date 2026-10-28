module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMarking
public import Theory.Representation.BinaryOffender.Defs
/-!
# Quadratic action of a full symplectic root pair

The full transvection roots in one isotropic plane lie in its elementary
radical. Their matrices have identity diagonal blocks and zero lower-left
block, so each displacement is fixed by the entire radical. This proves
quadraticity of every root pair over the original characteristic-two field.
The replacement application in CriticalReduction.RootProductQuadratic lifts
this through the whole central cover.
Source: MS93 (5.1), printed p.913.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
local notation "τ" => restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)

/-- The two full roots act quadratically on the binary natural module. -/
theorem root_pair_quadratic (s t : Option F) :
    IsQuadratic τ (rootImage s ⊔ rootImage t) := by
  have hle : rootImage s ⊔ rootImage t ≤ (wing true).map unipotent.subtype :=
    sup_le (map_mono (rootFamily_le_wing s)) (map_mono (rootFamily_le_wing t))
  intro a ha b hb v
  obtain ⟨a,hwa,rfl⟩ := hle ha
  obtain ⟨b,hwb,rfl⟩ := hle hb
  obtain ⟨⟨a₀,a₁,a₂,a₃⟩,rfl⟩ := element_surjective a
  obtain ⟨⟨b₀,b₁,b₂,b₃⟩,rfl⟩ := element_surjective b
  have ha₀ : a₀=0 := (element_mem_wing true _ _ _ _).mp hwa
  have hb₀ : b₀=0 := (element_mem_wing true _ _ _ _).mp hwb
  subst a₀; subst b₀
  change (element 0 a₁ a₂ a₃).val.val *ᵥ
      ((element 0 b₁ b₂ b₃).val.val *ᵥ v-v) =
    (element 0 b₁ b₂ b₃).val.val *ᵥ v-v
  rw [element_matrix,element_matrix]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
