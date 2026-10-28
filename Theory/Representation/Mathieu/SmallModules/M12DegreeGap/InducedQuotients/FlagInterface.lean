module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Coordinates
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Literal factor interfaces for the M₁₂ tensor model

The remaining finite calculation splits into an invariant flag on the actual
native action and density of the displayed diagonal matrix blocks. This
interface records the flag and the coordinates of its literal successive
quotients; it includes no assertion of irreducibility. The theorem below
combines it with independent full-matrix-algebra certificates.

Source context: the ordinary degree input to Aschbacher–Smith Chapter K,
printed p.457; James, J. Algebra 27 (1973), 57–111.
-/

public noncomputable section
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients
open CertificateData
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- The seven actual invariant quotient spaces, with their marked action matrices. -/
structure MatrixFlag {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) (d : Factor → ℕ) (g : Fin 2 → G)
    (A : ∀ t, Fin 2 → Matrix (Fin (d t)) (Fin (d t)) k) where
  stage : ℕ → Subrepresentation ρ
  zero : stage 0 = ⊥
  last : stage 7 = ⊤
  mono : ∀ m, m < 7 → stage m ≤ stage (m + 1)
  coordinates (t : Factor) :
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[k]
      (Fin (d t) → k)
  generator_coordinates : ∀ (t : Factor) (j : Fin 2) v,
    coordinates t
      ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation (g j) v) =
    (A t j).mulVec (coordinates t v)

/-- The flag interface specialized to the literal native action and the published blocks. -/
abbrev FlagCoordinates := MatrixFlag tensorAction degree actor factorMatrix

/-- Each factor is simple when its two displayed matrices generate its full algebra. -/
theorem filtration_of_flagCoordinates (C : FlagCoordinates)
    (hspan : ∀ (t : Factor)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree t)) (Fin (degree t)) (ZMod 2))),
      (∀ j, factorMatrix t j ∈ Q) → Q = ⊤) :
    FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction := by
  apply filtration_of_flag ({1, 10, 44} : Set ℕ) 7 C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_coordinate_matrices (degree_pos t) actor
      (factorMatrix t) (C.coordinates t) (C.generator_coordinates t) (hspan t)
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    rw [he]
    exact degree_allowed t

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients
