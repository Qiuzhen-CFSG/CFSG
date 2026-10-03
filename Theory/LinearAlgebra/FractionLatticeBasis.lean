module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Bases of full lattices over fraction fields

An integral basis of a submodule spanning a vector space over the fraction
field is also a basis of that vector space. Linear independence is preserved
by clearing denominators, and spanning follows by taking the field span of
the integral span. Coordinates of lattice vectors are the images of their
integral coordinates.

This is the linear algebra step in the invariant-lattice construction; see
Serre, *Linear Representations of Finite Groups*, Chapter 15. The fraction-field
hypothesis is essential: spanning alone over a larger field does not preserve
rank.
-/

public section

noncomputable section
namespace Submodule
variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
  [IsScalarTower R K V]

/-- A basis of a full lattice is a basis over the fraction field. -/
def fractionBasis (L : Submodule R V) (b : Module.Basis ι R L)
    (hL : Submodule.span K (L : Set V) = ⊤) : Module.Basis ι K V := by
  apply Module.Basis.mk
    ((LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)))
  have hs : Submodule.span R (Set.range fun i => (b i : V)) = L := by
    rw [show (Set.range fun i => (b i : V)) = L.subtype '' Set.range b by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  change ⊤ ≤ Submodule.span K (Set.range fun i => (b i : V))
  rw [← Submodule.span_span_of_tower R K, hs, hL]

@[simp] theorem fractionBasis_apply (L : Submodule R V) (b : Module.Basis ι R L)
    (hL : Submodule.span K (L : Set V) = ⊤) (i : ι) :
    L.fractionBasis b hL i = (b i : V) := Module.Basis.mk_apply _ _ _

@[simp] theorem fractionBasis_repr (L : Submodule R V) (b : Module.Basis ι R L)
    (hL : Submodule.span K (L : Set V) = ⊤) (x : L) (i : ι) :
    (L.fractionBasis b hL).repr (x : V) i = algebraMap R K (b.repr x i) := by
  classical
  let f : L →ₗ[R] K := ((L.fractionBasis b hL).coord i).restrictScalars R ∘ₗ L.subtype
  let f' : L →ₗ[R] K := (Algebra.linearMap R K).comp (b.coord i)
  have heq : f = f' := by
    apply b.ext
    intro j
    change (L.fractionBasis b hL).repr (b j : V) i = algebraMap R K (b.repr (b j) i)
    rw [← L.fractionBasis_apply b hL j]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun heq x
end Submodule

