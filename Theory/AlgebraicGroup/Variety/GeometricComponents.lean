module

public import Theory.AlgebraicGroup.Variety.ClosedLocus
public import Theory.AlgebraicGroup.Variety.GeometricDimension

/-!
# Irreducible components of geometric varieties

An irreducible component of a geometric variety has a canonical reduced geometric carrier:
apply `reducedClosedSubvariety` to its closed topological support.  The inclusion has exactly
that support.  Its source is homeomorphic first to the range of the closed immersion and then
to the component subtype, so `Subtype.irreducibleSpace` transports to both the
`IrreducibleSpace` and `PreirreducibleSpace` instances on the carrier.

Finite-type geometric varieties are Noetherian, hence have finitely many irreducible
components, whose union is the whole underlying scheme.  Besides the finite index and cover
statements, this module records the resulting gluing criterion: a subset is open precisely
when its pullback to every component is open.  This is the componentwise assembly interface
used for disconnected morphic-action orbit geometry.

The construction is the reduced-carrier form of the irreducible-component reduction in
Borovoi, *Linear Algebraic Groups* (`Bor1`), Proposition 1.8.  It uses only closed loci and
Noetherian topology; quotient descent is not involved.
-/

public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

/-- The type of irreducible components of a geometric variety. -/
abbrev IrreducibleComponent (V : Geometric k) :=
  {Z : Set V.toScheme // Z ∈ irreducibleComponents V.toScheme}

/-- The canonical reduced closed subvariety supported on an irreducible component. -/
def irreducibleComponentSubvariety (V : Geometric k)
    (Z : IrreducibleComponent V) : ClosedSubvariety V :=
  reducedClosedSubvariety V
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩

/-- The component carrier has exactly the chosen irreducible component as its range. -/
@[simp]
theorem irreducibleComponentSubvariety_range (V : Geometric k)
    (Z : IrreducibleComponent V) :
    Set.range (irreducibleComponentSubvariety V Z).inclusion.hom = Z.1 := by
  exact reducedClosedSubvariety_range V
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩

/-- The reduced geometric carrier of an irreducible component is irreducible. -/
instance irreducibleComponentSubvariety_irreducibleSpace
    (V : Geometric k) (Z : IrreducibleComponent V) :
    IrreducibleSpace
      (irreducibleComponentSubvariety V Z).toGeometric.toScheme := by
  let C := irreducibleComponentSubvariety V Z
  let e₁ : C.toGeometric.toScheme ≃ₜ Set.range C.inclusion.hom :=
    C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
  let e₂ : Set.range C.inclusion.hom ≃ₜ Z.1 :=
    Homeomorph.setCongr (by
      simp only [C]
      exact irreducibleComponentSubvariety_range V Z)
  exact ((e₁.trans e₂).irreducibleSpace_iff).mpr
    (Subtype.irreducibleSpace Z.2.1)

/-- The reduced geometric carrier of an irreducible component is preirreducible. -/
instance irreducibleComponentSubvariety_preirreducibleSpace
    (V : Geometric k) (Z : IrreducibleComponent V) :
    PreirreducibleSpace
      (irreducibleComponentSubvariety V Z).toGeometric.toScheme := by
  infer_instance

/-- A geometric variety has only finitely many irreducible components. -/
theorem irreducibleComponents_finite (V : Geometric k) :
    (irreducibleComponents V.toScheme).Finite :=
  NoetherianSpace.finite_irreducibleComponents

/-- The type indexing irreducible components of a geometric variety is finite. -/
instance finiteIrreducibleComponent (V : Geometric k) :
    Finite (IrreducibleComponent V) :=
  Set.finite_coe_iff.mpr (irreducibleComponents_finite V)

/-- The irreducible components cover the underlying topological space. -/
theorem irreducibleComponents_cover (V : Geometric k) :
    ⋃₀ irreducibleComponents V.toScheme = Set.univ :=
  sUnion_irreducibleComponents

/-- The finite component index presents the underlying space as an indexed union. -/
theorem iUnion_irreducibleComponent (V : Geometric k) :
    (⋃ Z : IrreducibleComponent V, Z.1) = Set.univ := by
  rw [← irreducibleComponents_cover V]
  ext x
  simp

private theorem isOpen_of_finite_isClosed_cover
    {X : Type u} [TopologicalSpace X] {C : Set (Set X)}
    (hCfin : C.Finite) (hCclosed : ∀ Z ∈ C, IsClosed Z)
    (hCcover : ⋃₀ C = Set.univ) {U : Set X}
    (hU : ∀ Z ∈ C, IsOpen (((↑) : Z → X) ⁻¹' U)) :
    IsOpen U := by
  rw [← isClosed_compl_iff]
  have hZUclosed : ∀ Z ∈ C, IsClosed (Z ∩ Uᶜ) := by
    intro Z hZ
    have hpre : IsClosed (((↑) : Z → X) ⁻¹' Uᶜ) := by
      simpa only [Set.preimage_compl] using (hU Z hZ).isClosed_compl
    have himage :=
      (hCclosed Z hZ).isClosedEmbedding_subtypeVal.isClosedMap _ hpre
    have heq :
        ((fun x : Z ↦ (x : X)) '' (((↑) : Z → X) ⁻¹' Uᶜ)) =
          Z ∩ Uᶜ := by
      ext x
      simp
    rw [← heq]
    exact himage
  have hcompl : Uᶜ = ⋃ Z ∈ C, Z ∩ Uᶜ := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃₀ C := by rw [hCcover]; trivial
      obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hxcover
      exact Set.mem_iUnion.mpr ⟨Z, Set.mem_iUnion.mpr ⟨hZ, hxZ, hx⟩⟩
    · intro hx
      obtain ⟨Z, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨-, -, hxU⟩ := Set.mem_iUnion.mp hx
      exact hxU
  rw [hcompl]
  exact hCfin.isClosed_biUnion hZUclosed

/-- A subset is open iff its pullback to every irreducible component is open. -/
theorem isOpen_iff_irreducibleComponent_preimage
    (V : Geometric k) {U : Set V.toScheme} :
    IsOpen U ↔ ∀ Z : IrreducibleComponent V,
      IsOpen (((↑) : Z.1 → V.toScheme) ⁻¹' U) := by
  constructor
  · intro hU Z
    exact hU.preimage continuous_subtype_val
  · intro hU
    exact isOpen_of_finite_isClosed_cover
      (irreducibleComponents_finite V)
      (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ)
      (irreducibleComponents_cover V)
      (fun Z hZ ↦ hU ⟨Z, hZ⟩)

end Theory.AlgebraicGroup.Variety.Geometric

end
