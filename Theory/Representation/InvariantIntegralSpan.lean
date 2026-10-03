module

public import Mathlib.LinearAlgebra.PID
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Invariant integral spans for finite representations

The span over a coefficient ring of all group translates of a finite spanning
family is finite, invariant, and still spans the original vector space. Over
a PID embedded in the coefficient field it is finite free, and restricting
the original action gives an integral representation on this module.

This is the orbit-span construction used in integral lattice reduction in
ordinary and modular representation theory (see Serre, *Linear Representations
of Finite Groups*, Chapter 15). It does not assert descent of a complex
irreducible representation to a specified fraction field. In particular, a
spanning integral module can have larger rank than the original vector space
when the coefficient field is larger than the fraction field of the ring.
-/

public section

noncomputable section
namespace Representation
variable (R : Type*) [CommRing R]
variable {K G V ι : Type*} [Field K] [Monoid G] [AddCommGroup V]
  [Module K V] [Module R V]

/-- The integral span of the translates of a family of vectors. -/
@[expose] def orbitSpan (ρ : Representation K G V) (v : ι → V) : Submodule R V :=
  Submodule.span R (Set.range fun p : G × ι => ρ p.1 (v p.2))

theorem mem_orbitSpan (ρ : Representation K G V) (v : ι → V) (g : G) (j : ι) :
    ρ g (v j) ∈ orbitSpan R ρ v :=
  Submodule.subset_span ⟨(g, j), rfl⟩

theorem generator_mem_orbitSpan (ρ : Representation K G V) (v : ι → V) (j : ι) :
    v j ∈ orbitSpan R ρ v := by
  simpa using mem_orbitSpan R ρ v 1 j

theorem orbitSpan_fg [Finite G] [Finite ι] (ρ : Representation K G V) (v : ι → V) :
    (orbitSpan R ρ v).FG := Submodule.fg_span (Set.finite_range _)

variable [Algebra R K] [IsScalarTower R K V]

theorem orbitSpan_apply_mem (ρ : Representation K G V) (v : ι → V)
    (g : G) {x : V} (hx : x ∈ orbitSpan R ρ v) : ρ g x ∈ orbitSpan R ρ v := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨h, j⟩, rfl⟩ := hy
    simpa only [map_mul, Module.End.mul_apply] using mem_orbitSpan R ρ v (g * h) j
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (orbitSpan R ρ v).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [(ρ g).map_smul_of_tower] using (orbitSpan R ρ v).smul_mem a ih

omit [Algebra R K] [IsScalarTower R K V] in
theorem span_orbitSpan_eq_top (ρ : Representation K G V) (v : ι → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span K (orbitSpan R ρ v : Set V) = ⊤ := by
  apply top_unique
  rw [← hv]
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  exact generator_mem_orbitSpan R ρ v j

/-- The original action restricted to its invariant integral span. -/
@[expose] def orbitSpanRepresentation (ρ : Representation K G V) (v : ι → V) :
    Representation R G (orbitSpan R ρ v) where
  toFun g := ((ρ g).restrictScalars R).restrict (fun _ hx => orbitSpan_apply_mem R ρ v g hx)
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem orbitSpanRepresentation_apply (ρ : Representation K G V) (v : ι → V)
    (g : G) (x : orbitSpan R ρ v) :
    (orbitSpanRepresentation R ρ v g x : V) = ρ g x := rfl

instance orbitSpan_finite [Finite G] [Finite ι]
    (ρ : Representation K G V) (v : ι → V) : Module.Finite R (orbitSpan R ρ v) :=
  Module.Finite.iff_fg.mpr (orbitSpan_fg R ρ v)

instance orbitSpan_free [IsDomain R] [IsPrincipalIdealRing R] [FaithfulSMul R K]
    [Finite G] [Finite ι] (ρ : Representation K G V) (v : ι → V) :
    Module.Free R (orbitSpan R ρ v) := by
  let := Module.IsTorsionFree.trans_faithfulSMul R K V
  exact Module.free_of_finite_type_torsion_free'

/-- Every finite-dimensional representation of a finite monoid has a finite
invariant integral span. Freeness follows over a PID with injective coefficient map. -/
theorem exists_finite_invariant_span [Finite G] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ L : Submodule R V, L.FG ∧ Submodule.span K (L : Set V) = ⊤ ∧
      ∀ g : G, ∀ x ∈ L, ρ g x ∈ L := by
  let b := Module.finBasis K V
  exact ⟨orbitSpan R ρ b, orbitSpan_fg R ρ b,
    span_orbitSpan_eq_top R ρ b b.span_eq, fun g _ hx => orbitSpan_apply_mem R ρ b g hx⟩
end Representation
