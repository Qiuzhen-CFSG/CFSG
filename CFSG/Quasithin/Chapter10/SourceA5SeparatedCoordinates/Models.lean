module
public import Theory.Representation.NormalPairHomogeneous
public import CFSG.Quasithin.Chapter10.SourceA5IrreducibleTwists
public import CFSG.Quasithin.Chapter10.SourceA5ProductTypeAlternatives

/-!
# Exact model coordinates for separated binary A₅ pairs

A simple constituent of the first support is nontrivial by faithfulness.
G.9.3 makes every automorphism twist equivalent to that same constituent, so
the normal-pair homogeneity theorem supplies both supports as equally many
copies. The natural/deleted classifier then changes every copy by its literal
intertwiner. Multiplicity is positive but remains arbitrary.

This supplies the separated full-quotient coordinate input to the source
full/local passage, before any local irreducibility or multiplicity bound.
Source: Aschbacher–Smith D.3.5–6, D.3.21 and 3.2.6, pp.195–196,206,581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.NormalPairHomogeneous
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V)
  (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)

/-- Both supports are equally many copies of the same exact natural or deleted
binary A₅ model. All factor actions are the original marked actions. -/
theorem source_a5_separated_model_coordinates
    (hi : Function.Injective i) [i.range.Normal] [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hL : NormalPairSupport.left ρ i ≠ ⊥)
    (exchange : NormalPairSupport.left ρ i ≃ₗ[ZMod 2] NormalPairSupport.right ρ i) :
    (∃ f : alternatingGroup (Fin 5) ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Coordinates ρ i (SL2.BinarySmall.natural.comp f.toMonoidHom))) ∨
    Nonempty (Coordinates ρ i BinaryPermutation.FiveTensorSquare.δ) := by
  classical
  obtain ⟨A,hA,f,hf⟩ := exists_simple_left_type ρ i hL
  let σ := A.toRepresentation
  let : σ.IsIrreducible := hA
  have hZ : center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  have hn : ∃ s, σ s ≠ 1 := left_type_nontrivial ρ i σ hi hρ f hf
  obtain ⟨C⟩ := pair_copy_coordinates ρ i σ hi hZ hρ
    (fun a => source_a5_irreducible_twist σ (MulEquiv.refl _) a) f hf exchange
  rcases source_a5_irreducible_natural_or_deleted σ hn with hnat | hdel
  · obtain ⟨g,⟨e⟩⟩ := hnat
    exact Or.inl ⟨g,⟨Coordinates.changeModel ρ i σ C e⟩⟩
  · obtain ⟨e⟩ := hdel
    exact Or.inr ⟨Coordinates.changeModel ρ i σ C e⟩

end CFSG.Quasithin.Chapter10
