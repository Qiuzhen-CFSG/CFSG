module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Contracts
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Parameters
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.MatrixFacts
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
public import Mathlib.RepresentationTheory.Character

/-!
# Assembly of the four degree-sixteen PSL₃(3) models

The native-action and matrix-density certificates have separate mathematical
roles. An action realizing the two marked matrices is irreducible by density.
Every algebraically closed field of characteristic two contains four distinct
Frobenius-conjugate parameters satisfying `t⁴=t+1`. At the specified native
generator product the trace is `s=t³+t+1`; since `s+s²=t`, these four traces
are distinct. Thus the four actions are pairwise inequivalent.

The final theorem `sixteenModelsExist` supplies the exact `SixteenModelsExist`
input consumed by `AbsoluteDegrees.small_degree_of_models`. The checked native
edge table discharges `ActionsExist`, and the rank-one spanning certificate
discharges `GeneratorDensity`, so the construction has no additional premises.

Source: GM02, *Classification of 2F-modules I*, Proposition 4.2, manuscript
pp.9–10, and the four defect-zero degree-sixteen rows of the L₃(3) mod-2
decomposition matrix. Numerical generator data and attribution are in `Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
universe v
variable {F : Type*} [Field F]

/-- A matrix-algebra density certificate proves density for the literal action. -/
theorem action_dense_of_realizes (t : F)
    (ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F)) (hρ : Realizes t ρ)
    (hd : Algebra.adjoin F ({matrixA t, matrixB t} : Set (Matrix (Fin 16) (Fin 16) F)) = ⊤) :
    Algebra.adjoin F (Set.range ρ) = ⊤ := by
  let S := Algebra.adjoin F (Set.range ρ)
  have hle : Algebra.adjoin F ({matrixA t, matrixB t} :
      Set (Matrix (Fin 16) (Fin 16) F)) ≤
      S.comap Matrix.toLinAlgEquiv'.toAlgHom := by
    apply Algebra.adjoin_le
    intro M hM
    rcases hM with rfl | hM
    · change Matrix.toLin' (matrixA t) ∈ S
      rw [← hρ.1, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self generatorA)
    · have hM' : M = matrixB t := hM
      subst M
      change Matrix.toLin' (matrixB t) ∈ S
      rw [← hρ.2, Matrix.toLin'_toMatrix']
      exact Algebra.subset_adjoin (Set.mem_range_self generatorB)
  apply top_unique
  intro f _
  have hm : LinearMap.toMatrix' f ∈ Algebra.adjoin F
      ({matrixA t, matrixB t} : Set (Matrix (Fin 16) (Fin 16) F)) := by
    rw [hd]
    trivial
  have hf := hle hm
  change Matrix.toLin' (LinearMap.toMatrix' f) ∈ S at hf
  simpa only [Matrix.toLin'_toMatrix'] using hf

/-- Simplicity uses the literal generator action and the full algebra certificate. -/
theorem irreducible_of_realizes (t : F)
    (ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F)) (hρ : Realizes t ρ)
    (hd : Algebra.adjoin F ({matrixA t, matrixB t} : Set (Matrix (Fin 16) (Fin 16) F)) = ⊤) :
    IsIrreducible ρ :=
  irreducible_of_jacobson_density_surjective ρ (action_dense_of_realizes t ρ hρ hd)

/-- Trace at the specified native group element; no model identification is implicit. -/
theorem character_product_of_realizes [CharP F 2] (t : F) (ht : t ^ 4 = t + 1)
    (ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F)) (hρ : Realizes t ρ) :
    ρ.character (generatorA * generatorB) = traceParameter t := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace F (Pi.basisFun F (Fin 16))]
  change (LinearMap.toMatrix' (ρ (generatorA * generatorB))).trace = _
  rw [map_mul, LinearMap.toMatrix'_mul, hρ.1, hρ.2]
  exact trace_matrix_product t ht

/-- Four Frobenius parameters give inequivalent actions, detected by one trace. -/
theorem pairwise_inequivalent_of_realizes [CharP F 2] (t : F) (ht : t ^ 4 = t + 1)
    (ρ : Fin 4 → Representation F Matrix.PSL3Three.PSL (Fin 16 → F))
    (hρ : ∀ i, Realizes (t ^ (2 ^ i.val)) (ρ i)) :
    Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
  intro i j hij
  constructor
  intro e
  have h := congrFun (Representation.char_iso e) (generatorA * generatorB)
  rw [character_product_of_realizes _ (orbit_parameter t ht i) _ (hρ i),
    character_product_of_realizes _ (orbit_parameter t ht j) _ (hρ j)] at h
  exact hij (traceParameter_orbit_injective t ht h)

/-- Conditional assembly for the exact native construction contract. The action
and matrix-algebra certificates are mathematically independent inputs. -/
theorem sixteenModelsExist_of_certificates (ha : ActionsExist.{v})
    (hd : GeneratorDensity.{v}) : SixteenModelsExist.{v} := by
  intro F _ _ _
  obtain ⟨t, ht⟩ := exists_parameter (F := F)
  have hact (i : Fin 4) := ha F (t ^ (2 ^ i.val)) (orbit_parameter t ht i)
  choose ρ hρ using hact
  refine ⟨ρ, ?_, pairwise_inequivalent_of_realizes t ht ρ hρ⟩
  intro i
  exact irreducible_of_realizes _ _ (hρ i) (hd F _ (orbit_parameter t ht i))

/-- Four pairwise inequivalent irreducible degree-sixteen representations of
the literal PSL₃(3) quotient over every algebraically closed field of
characteristic two. The native-action and density certificates are discharged. -/
theorem sixteenModelsExist : SixteenModelsExist.{v} :=
  sixteenModelsExist_of_certificates NativeAction.actionsExist generatorDensity

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
