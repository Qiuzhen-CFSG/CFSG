module

public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.SmallMovedProducts

/-!
# Scalar restriction preserves whole moved spaces

Every scalar multiple of an action difference is again an action difference.
The commutator span over the prime field is therefore already closed under
the larger field. Consequently the moved dimension and the fixed codimension
both multiply by the defining-field degree on scalar restriction.

Source application: the F4-linear covered-A6 exclusion in 13.7.15(1).
-/

public section
namespace Representation
variable {k F G V : Type*} [Field k] [Field F] [Algebra k F] [Group G]
  [AddCommGroup V] [Module F V] [Module k V] [IsScalarTower k F V]
  (ρ : Representation F G V)

/-- Restriction of scalars does not enlarge the actual commutator subspace. -/
theorem coinvariantsKer_restrictScalars :
    Coinvariants.ker (restrictScalars (k := k) ρ) = (Coinvariants.ker ρ).restrictScalars k := by
  let C := Coinvariants.ker (restrictScalars (k := k) ρ)
  have hs (a : F) (w : V) (hw : w ∈ C) : a • w ∈ C := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨g,v⟩,rfl⟩ := hw
      change a • (ρ g v - v) ∈ C
      rw [smul_sub, ← map_smul]
      exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g (a • v)
    | zero => simpa only [smul_zero] using C.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using C.add_mem hx hy
    | smul r x _ hx => simpa only [smul_comm a r] using C.smul_mem r hx
  let CF : Submodule F V :=
    { carrier := C
      zero_mem' := C.zero_mem
      add_mem' := C.add_mem
      smul_mem' := hs }
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ) g v
  · have hh : Coinvariants.ker ρ ≤ CF := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g v
    exact hh

end Representation

namespace Representation.BinaryOffender
variable {F G V : Type*} [Field F] [Algebra (ZMod 2) F] [Group G]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V]
  (ρ : Representation F G V)

/-- Exact prime-field dimension of the whole moved space. -/
theorem moved_finrank_restrictScalars (A : Subgroup G) :
    Module.finrank (ZMod 2) (subspaceCommutator (restrictScalars (k := ZMod 2) ρ) ⊤ A) =
      Module.finrank (ZMod 2) F * Module.finrank F (Coinvariants.ker (ρ.comp A.subtype)) := by
  rw [subspaceCommutator_top_eq_coinvariants]
  change Module.finrank (ZMod 2) (Coinvariants.ker (restrictScalars (k := ZMod 2) (ρ.comp A.subtype))) = _
  rw [coinvariantsKer_restrictScalars]
  exact (Module.finrank_mul_finrank (ZMod 2) F (Coinvariants.ker (ρ.comp A.subtype))).symm

/-- Exact prime-field codimension of fixed vectors. -/
theorem fixedCodim_restrictScalars (A : Subgroup G) :
    fixedCodim (restrictScalars (k := ZMod 2) ρ) A =
      Module.finrank (ZMod 2) F * Module.finrank F (V ⧸ Representation.invariants (ρ.comp A.subtype)) := by
  let C := Representation.invariants (ρ.comp A.subtype)
  have he : fixedSpace (restrictScalars (k := ZMod 2) ρ) A = C.restrictScalars (ZMod 2) := rfl
  rw [fixedCodim,he,(Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).finrank_eq]
  exact (Module.finrank_mul_finrank (ZMod 2) F (V ⧸ C)).symm
end Representation.BinaryOffender
