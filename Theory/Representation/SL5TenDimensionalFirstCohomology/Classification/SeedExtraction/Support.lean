module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Empty
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Endpoints
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Dimension restrictions on binary SL₅ highest-vector support

The support of a nonzero local highest vector in an irreducible ten-dimensional
module is a singleton at one of the two middle roots. Empty support forces
dimension one. The five-translate invariant span in `Support.Endpoints` bounds
endpoint singleton support by dimension five. The independent vectors in
`Support.Multiple` force dimension at least eleven for multiple-root support.
The final theorem discharges both estimates in the conditional assembly lemma.

The application is Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(7), printed p.408/PDF p.419. The existence of a local highest vector and
identification with an exterior model are separate from this dimension argument.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A nonzero local highest vector in an irreducible ten-dimensional module has
nonempty support. -/
theorem LocalHighestVector.nonempty_of_finrank_ten
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hdim : Module.finrank (ZMod 2) V = 10) : J.Nonempty := by
  by_contra hempty
  have hJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  subst J
  have := h.finrank_eq_one_of_empty hv
  omega

/-- Assemble the support restriction from explicit endpoint and multiple-root
dimension estimates. -/
theorem LocalHighestVector.support_eq_boundaryRoot_of_dimension_bounds
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hdim : Module.finrank (ZMod 2) V = 10)
    (hendpoint : ∀ i : Fin 4, (i = 0 ∨ i = 3) → J = {i} →
      Module.finrank (ZMod 2) V ≤ 5)
    (hmultiple : 2 ≤ J.card → 11 ≤ Module.finrank (ZMod 2) V) :
    ∃ a : Fin 2, J = {boundaryRoot a} := by
  have hpos := Finset.card_pos.mpr (h.nonempty_of_finrank_ten hv hdim)
  have hcard : J.card = 1 := by
    by_contra hn
    have := hmultiple (by omega)
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  fin_cases i
  · have := hendpoint 0 (Or.inl rfl) hi
    omega
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · have := hendpoint 3 (Or.inr rfl) hi
    omega

/-- In an irreducible ten-dimensional binary SL₅ module, every nonzero local
highest vector has singleton support at one of the two middle roots. -/
theorem LocalHighestVector.support_eq_boundaryRoot_of_finrank_ten
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hdim : Module.finrank (ZMod 2) V = 10) :
    ∃ a : Fin 2, J = {boundaryRoot a} := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  apply h.support_eq_boundaryRoot_of_dimension_bounds hv hdim
  · intro i hi hJ
    exact (hJ ▸ h).finrank_le_five_of_endpoint hv hi
  · exact h.eleven_le_finrank_of_multiple hv

end Representation.SL5TenDimensional.Classification
