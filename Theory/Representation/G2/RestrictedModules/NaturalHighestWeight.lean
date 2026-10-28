module

public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization

/-!
# The natural G₂ highest weight in octonion coordinates

The simple positive roots are Wilson's F (short) and E (long). Their characters
are `l/m` and `m²/l` on `torus l m`. The simple coroots below give the Cartan
pairings `(2,-3)` and `(-1,2)`. The highest vector of the natural module has
character `l`, hence coroot pairings `(1,0)` in short-then-long order. This is
GLS3's `λ₂`, whereas its adjoint `λ₁` has pairings `(0,1)`.

The highest line is proved directly: invariance under E(1) and F(1) kills the
other five coordinates. Every positive root fixes its remaining basis vector.
Source: GLS3, Example 2.8.10(g), with the ATLAS root conventions.
-/

@[expose] public section

namespace Atlas.G2.Restricted

variable {F : Type*} [Field F]

/-- Simple coroot for Wilson F, the short simple root. -/
def shortCoroot (t : Fˣ) : Model F := torus t t⁻¹

/-- Simple coroot for Wilson E, the long simple root. -/
def longCoroot (t : Fˣ) : Model F := torus 1 t

/-- The short simple root has pairing 2 with its coroot. -/
theorem shortCoroot_rootF (t : Fˣ) (a : F) :
    shortCoroot t * rootF a * (shortCoroot t)⁻¹ = rootF ((t : F)^2 * a) := by
  rw [shortCoroot, torus_rootF]
  congr 1
  simp [div_eq_mul_inv, pow_two]

/-- The long simple root has pairing -3 with the short coroot. -/
theorem shortCoroot_rootE (t : Fˣ) (a : F) :
    shortCoroot t * rootE a * (shortCoroot t)⁻¹ = rootE (((t : F)⁻¹)^3 * a) := by
  rw [shortCoroot, torus_rootE]
  congr 1
  simp [div_eq_mul_inv, pow_succ]

/-- The short simple root has pairing -1 with the long coroot. -/
theorem longCoroot_rootF (t : Fˣ) (a : F) :
    longCoroot t * rootF a * (longCoroot t)⁻¹ = rootF ((t : F)⁻¹ * a) := by
  rw [longCoroot, torus_rootF]
  simp

/-- The long simple root has pairing 2 with its coroot. -/
theorem longCoroot_rootE (t : Fˣ) (a : F) :
    longCoroot t * rootE a * (longCoroot t)⁻¹ = rootE ((t : F)^2 * a) := by
  rw [longCoroot, torus_rootE]
  simp

namespace NaturalCoordinates

variable (F) [CharP F 2]

/-- A nonzero vector on the natural highest line. -/
def highestVector : Space F := Pi.single 0 1

omit [CharP F 2] in
theorem highestVector_ne_zero : highestVector F ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [highestVector] at this

/-- The complete torus action, with the six actual weights. -/
theorem action_torus (l m : Fˣ) (v : Space F) :
    action F (torus l m) v =
      ![(l : F) * v 0, (m : F) * v 1, (l * m⁻¹ : Fˣ) * v 2,
        (l⁻¹ * m : Fˣ) * v 3, (m⁻¹ : Fˣ) * v 4, (l⁻¹ : Fˣ) * v 5] := by
  ext i
  fin_cases i <;>
    simp [action_apply, projection, representative, Natural.traceZeroAction_val,
      torus, torusEquiv, torusLinear, torusWeights]

/-- All six positive root subgroups fix the highest vector. -/
theorem highestVector_fixed_roots (a : F) :
    action F (rootA a) (highestVector F) = highestVector F ∧
    action F (rootB a) (highestVector F) = highestVector F ∧
    action F (rootC a) (highestVector F) = highestVector F ∧
    action F (rootD a) (highestVector F) = highestVector F ∧
    action F (rootE a) (highestVector F) = highestVector F ∧
    action F (rootF a) (highestVector F) = highestVector F := by
  simp only [action_rootA, action_rootB, action_rootC, action_rootD, action_rootE,
    action_rootF, highestVector]
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor
  · ext i; fin_cases i <;> simp
  constructor <;> ext i <;> fin_cases i <;> simp

/-- The complete positive unipotent group fixes the highest vector. -/
theorem highestVector_fixed_unipotentProduct (t : Fin 6 → F) :
    action F (unipotentProduct t) (highestVector F) = highestVector F := by
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [(highestVector_fixed_roots F _).2.2.2.2.2,
    (highestVector_fixed_roots F _).2.2.2.2.1,
    (highestVector_fixed_roots F _).2.2.2.1,
    (highestVector_fixed_roots F _).2.2.1,
    (highestVector_fixed_roots F _).2.1,
    (highestVector_fixed_roots F _).1]

/-- The highest line is already the common fixed space of two root elements. -/
theorem fixed_simpleRoots_iff (v : Space F) :
    (action F (rootE 1) v = v ∧ action F (rootF 1) v = v) ↔
      ∃ a : F, v = a • highestVector F := by
  constructor
  · rintro ⟨hE, hF⟩
    have h2 : v 2 = 0 := by
      have h := congrFun hE 1
      simpa using h
    have h4 : v 4 = 0 := by
      have h := congrFun hE 3
      simpa using h
    have h1 : v 1 = 0 := by
      have h := congrFun hF 0
      simpa using h
    have h3 : v 3 = 0 := by
      have h := congrFun hF 2
      simpa using h
    have h5 : v 5 = 0 := by
      have h := congrFun hF 4
      simpa using h
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [highestVector, h1, h2, h3, h4, h5]
  · rintro ⟨a, rfl⟩
    simp only [map_smul, (highestVector_fixed_roots F 1).2.2.2.2.1,
      (highestVector_fixed_roots F 1).2.2.2.2.2, and_self]

/-- The highest weight is the character `l` on the marked two-parameter torus. -/
theorem highestVector_torus (l m : Fˣ) :
    action F (torus l m) (highestVector F) = (l : F) • highestVector F := by
  ext i
  fin_cases i <;> simp [action_torus, highestVector]

/-- Short-coroot pairing 1: GLS3 calls this natural highest weight λ₂. -/
theorem highestVector_shortCoroot (t : Fˣ) :
    action F (shortCoroot t) (highestVector F) = (t : F) • highestVector F :=
  highestVector_torus F _ _

/-- Long-coroot pairing 0 for the natural highest weight. -/
theorem highestVector_longCoroot (t : Fˣ) :
    action F (longCoroot t) (highestVector F) = highestVector F := by
  simpa [longCoroot] using highestVector_torus F 1 t

end NaturalCoordinates
end Atlas.G2.Restricted
