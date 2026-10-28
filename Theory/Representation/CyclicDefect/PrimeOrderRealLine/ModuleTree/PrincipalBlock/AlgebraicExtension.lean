module

public import Theory.Character.ModularBlock.FiniteFieldExtension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Principal idempotents over an algebraic extension of a finite field

A proposed central idempotent factor has finitely many coefficients. Adjoining
those coefficients gives a finite field, where the Galois descent theorem
preserves augmentation-one primitivity. Injectivity of coefficient extension
then identifies the original factor. This includes the literal algebraic
closure without identifying it with a finite field.

Source: the scalar-extension step in Feit III.8--9; the finite-field step is
`ModularBlock.FiniteFieldPrimitivity`.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock

/-- Principal primitivity survives an algebraic extension of a finite field. -/
theorem map_isCentrallyPrimitive_of_algebraic
    (k K : Type*) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (G : Type*) [Group G] [Finite G]
    (e : MonoidAlgebra k G) (he : IsCentrallyPrimitive e)
    (haug : groupAlgebraAugmentation k G e = 1) :
    IsCentrallyPrimitive (MonoidAlgebra.mapRingHom G (algebraMap k K) e) := by
  classical
  let E := MonoidAlgebra.mapRingHom G (algebraMap k K) e
  have hEcenter : E ∈ Set.center (MonoidAlgebra K G) :=
    groupAlgebra_mapRingHom_mem_center (algebraMap k K) e he.1
  have hEidem : IsIdempotentElem E := he.2.1.map _
  have hEaug : groupAlgebraAugmentation K G E = 1 := by
    rw [groupAlgebraAugmentation_mapRingHom, haug, map_one]
  have hEne : E ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hEaug
    exact zero_ne_one hEaug
  refine ⟨hEcenter, hEidem, hEne, ?_⟩
  intro f hf hid hfactor hne
  let L := IntermediateField.adjoin k (Set.range f.coeff)
  let : Finite (Set.range f.coeff) := (Set.finite_range f.coeff).to_subtype
  let : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let : Finite L := Module.finite_of_finite k
  let q : L →+* K := L.val.toRingHom
  let Q := MonoidAlgebra.mapRingHom G q
  have hQ : Function.Injective Q :=
    MonoidAlgebra.map_injective q.toAddMonoidHom q.injective
  obtain ⟨fL, hfL⟩ : ∃ fL : MonoidAlgebra L G, Q fL = f := by
    have hcoeff : ∀ g, f.coeff g ∈ Set.range q := by
      intro g
      exact ⟨⟨f.coeff g, IntermediateField.subset_adjoin k _ ⟨g, rfl⟩⟩, rfl⟩
    have hmem : f ∈ Set.range (MonoidAlgebra.map (M := G) q.toAddMonoidHom) := by
      rw [MonoidAlgebra.range_map]
      exact hcoeff
    exact hmem
  let eL := MonoidAlgebra.mapRingHom G (algebraMap k L) e
  have heL : IsCentrallyPrimitive eL :=
    FiniteFieldPrimitivity.map_isCentrallyPrimitive_of_augmentation_eq_one k L G e he haug
  have heLmap : Q eL = E := by
    ext g
    rfl
  have hfLcenter : fL ∈ Set.center (MonoidAlgebra L G) := by
    apply Semigroup.mem_center_iff.mpr
    intro a
    apply hQ
    rw [map_mul, map_mul, hfL]
    exact Semigroup.mem_center_iff.mp hf (Q a)
  have hfLid : IsIdempotentElem fL := by
    apply hQ
    rw [map_mul, hfL, hid]
  have hfLfactor : fL * eL = fL := by
    apply hQ
    rw [map_mul, hfL, heLmap, hfactor]
  have hfLne : fL ≠ 0 := by
    intro hz
    apply hne
    rw [← hfL, hz, map_zero]
  have h := heL.2.2.2 fL hfLcenter hfLid hfLfactor hfLne
  exact hfL.symm.trans ((congrArg Q h).trans heLmap)

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
