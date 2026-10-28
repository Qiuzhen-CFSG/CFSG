module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.FlagInterface
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.MatrixChecks
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Flag
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.FactorAlgebras

/-!
# Small simple quotients of the literal induced M₁₁ heart

The actual induction is equivariantly identified with the native twelve-fiber
heart action. An invariant filtration with simple factors of degrees 1, 10
and 44 then excludes quotient degrees eleven through twenty-four. No
semisimplicity or absolute irreducibility of an arbitrary quotient is used.

The checked native flag and the seven full-matrix-algebra certificates now
supply that filtration without extra premises. Every simple quotient has
degree 1, 10 or 44, so a quotient of degree at most 24 has degree at most ten.
The final application uses the exact inverse-Frobenius map of the restriction
consumer; the separate M₁₁ degree calculation is not used here.
Source context: James, J. Algebra 27 (1973), 57–111, and the ordinary degree
input to Aschbacher–Smith Chapter K, printed pp.451 and 457.
-/

public noncomputable section
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients
open Sporadic.Mathieu M12Recognition CertificateData

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A filtration of the native model controls the literal induced-module quotient. -/
theorem quotient_finrank_mem_of_filtration
    (hfil : FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction)
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (q : inducedHeart.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) V ∈ ({1, 10, 44} : Set ℕ) := by
  let f := q.comp inducedTensorEquiv.symm.toIntertwiningMap
  have hs : Function.Surjective f := hq.comp inducedTensorEquiv.symm.toLinearEquiv.surjective
  have hn : f ≠ 0 := by
    intro hz
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := hs v
    apply hv
    rw [← hw]
    exact congrArg (fun k : tensorAction.IntertwiningMap σ => k w) hz
  exact hfil.finrank_mem f hn

/-- The required quotient bound, conditional only on the native finite filtration. -/
theorem finrank_le_ten_of_filtration
    (hfil : FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction)
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (q : inducedHeart.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  have h := quotient_finrank_mem_of_filtration hfil σ q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  omega

/-- Concrete assembly from the independent flag and matrix-density calculations. -/
theorem finrank_le_ten_of_flag_and_density
    (C : FlagCoordinates)
    (hspan : ∀ (t : Factor)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree t)) (Fin (degree t)) (ZMod 2))),
      (∀ j, factorMatrix t j ∈ Q) → Q = ⊤)
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (q : inducedHeart.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  finrank_le_ten_of_filtration (filtration_of_flagCoordinates C hspan) σ hd q hq

/-- Apply the finite reduction to the exact inverse-Frobenius map constructed
from a nonzero marked point-module intertwiner by the restriction consumer. -/
theorem finrank_le_ten_of_point_map_and_filtration
    (hfil : FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction)
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) (hf : f ≠ 0) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  finrank_le_ten_of_filtration hfil σ hd (inducePointMap σ f)
    (inducePointMap_surjective σ f hf)

/-- The checked native flag has simple factors of degrees one, ten and forty-four. -/
theorem nativeFiltration :
    FactorDegreeFiltration ({1, 10, 44} : Set ℕ) tensorAction :=
  factorDegreeFiltration_of_flagCoordinates nativeFlag

/-- Every simple quotient of the literal M₁₁ induction has one of these three degrees. -/
theorem quotient_finrank_mem
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (q : inducedHeart.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) V ∈ ({1, 10, 44} : Set ℕ) :=
  quotient_finrank_mem_of_filtration nativeFiltration σ q hq

/-- The small-simple-quotient bound for the literal induced M₁₁ point module.
This discharges the induced-quotient branch of
`finrank_le_ten_or_inducedHeart_quotient_of_point_degrees`. -/
theorem finrank_le_ten
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (q : inducedHeart.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  finrank_le_ten_of_filtration nativeFiltration σ hd q hq

/-- Apply the unconditional bound to the actual inverse-Frobenius surjection
from a nonzero marked point-module map. No semisimplicity of restriction is needed. -/
theorem finrank_le_ten_of_point_map
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) (hf : f ≠ 0) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  finrank_le_ten_of_point_map_and_filtration nativeFiltration σ hd f hf

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients
