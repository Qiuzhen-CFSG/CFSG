module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.NormFree
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Interface
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.Restriction

/-!
# The binary M₁₁ degree window from its eleven-coset filtration

The norm-zero case is the proved ten-dimensional point module. Every other
simple module is a quotient of the literal 720-dimensional eleven-coset
module. A genuine filtration of that module with simple factors of degrees
1, 10, 32 and 44 therefore excludes all other degrees through 24.

The independently proved native flag and matrix-simplicity certificates
construct this filtration without extra premises. The resulting degree
theorem applies to every simple submodule of the literal M₁₁ restriction
of an M₁₂ module in the degree window; restriction need not be semisimple.
Source: James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57–111. In characteristic two the degree-sixteen
ATLAS modules are over GF(4), so their binary degree is 32.
-/

public section
open Sporadic.Mathieu
open Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_eq_one_or_ten_of_filtration
    (hfil : FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation)
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 10 := by
  by_cases hn : τ.asAlgebraHom elevenNorm = 0
  · exact Or.inr (finrank_eq_ten_of_elevenNorm_eq_zero τ hn)
  obtain ⟨f, hf⟩ := exists_coset_map_of_elevenNorm_ne_zero τ hn
  have hf0 : f ≠ 0 := by
    intro hz
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨x, hx⟩ := hf v
    exact hv (hx.symm.trans (congrArg (fun k : cosetRepresentation.IntertwiningMap τ => k x) hz))
  have h := hfil.finrank_mem f hf0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  omega

/-- The exact small binary window from the two independent finite certificates.
Neither certificate is assumed to have been constructed by this theorem. -/
theorem finrank_eq_one_or_ten_of_certificates
    (C : FlagCoordinates) (hsimple : Data.SimpleMatrices)
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 10 :=
  finrank_eq_one_or_ten_of_filtration (filtration_of_certificates C hsimple) τ hd

/-- The actual eleven-coset module has a filtration with simple factors of
binary dimensions 1, 10, 32 and 44. Both finite certificates are discharged. -/
theorem factorDegreeFiltration :
    FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation :=
  filtration_of_simpleMatrices FactorSimplicity.simpleMatrices

/-- Every irreducible binary M₁₁ module of dimension at most 24 has dimension
one or ten. No faithfulness, norm or certificate premise is required. -/
theorem finrank_eq_one_or_ten
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 10 :=
  finrank_eq_one_or_ten_of_filtration factorDegreeFiltration τ hd

/-- Application to the actual point restriction, without assuming it semisimple.
The original degree window bounds every simple submodule of that restriction. -/
theorem point_fixed_or_point_map_of_certificates [FiniteDimensional (ZMod 2) V]
    (C : FlagCoordinates) (hsimple : Data.SimpleMatrices)
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Representation.invariants (σ.comp M12Recognition.pointEmbedding) ≠ ⊥ ∨
      ∃ f : M12Recognition.pointRepresentation.IntertwiningMap
        (σ.comp M12Recognition.pointEmbedding), f ≠ 0 := by
  apply point_fixed_or_point_map_of_simple_degrees σ
  intro S hS
  let : S.toRepresentation.IsIrreducible := hS
  exact finrank_eq_one_or_ten_of_certificates C hsimple S.toRepresentation
    ((Submodule.finrank_le S.toSubmodule).trans hd)

/-- Unconditional application to the literal M₁₁ restriction. This supplies
the fixed-vector or point-module map used by the M₁₂ degree-gap reduction. -/
theorem point_fixed_or_point_map [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Representation.invariants (σ.comp M12Recognition.pointEmbedding) ≠ ⊥ ∨
      ∃ f : M12Recognition.pointRepresentation.IntertwiningMap
        (σ.comp M12Recognition.pointEmbedding), f ≠ 0 :=
  point_fixed_or_point_map_of_certificates flagCoordinates
    FactorSimplicity.simpleMatrices σ hd

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees
