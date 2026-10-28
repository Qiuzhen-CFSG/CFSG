module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag.Construction

/-!
# The field filtration of the dual induced point module

The first 45 and 51 columns of the certified basis give invariant subspaces
of dimensions 45 and 51 in the actual 66-dimensional induction. Their
literal successive quotients have the published factor actions in the order
45, 6, 15. Full matrix algebras for those actions imply irreducibility and
assemble the requested factor-degree filtration.

The matrix-algebra assertion is the sole explicit extra premise. Its
independent producer and the parent dual-filtration module own its discharge
and binary scalar restriction. No splitting or pre-existing composition-factor
catalogue is assumed. Source context: Guralnick–Malle, Classification of
2F-modules I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7. The particular
induced flag is an independent calculation; provenance is in `source/README.md`.
-/

@[expose] public noncomputable section
open Representation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
open Uniqueness.PointRestriction.PointModel
/-- The literal invariant flag cut out by the first 45 and 51 saved basis columns. -/
def fieldFlag : ℕ → Subrepresentation (fieldRepresentation .dual) :=
  FieldFlag.stage FieldFlag.basisCoordinates FieldFlag.basisCoordinates_generator FieldFlag.upper
lemma fieldFlag_zero : fieldFlag 0 = ⊥ :=
  FieldFlag.stage_zero _ _ _
lemma fieldFlag_last : fieldFlag 3 = ⊤ :=
  FieldFlag.stage_last _ _ _
lemma fieldFlag_mono (m : ℕ) (hm : m < 3) : fieldFlag m ≤ fieldFlag (m+1) :=
  FieldFlag.stage_mono _ _ _ m hm
lemma fieldFlag_finrank (m : ℕ) :
    Module.finrank F (fieldFlag m).toSubmodule = FieldFlag.cut m :=
  FieldFlag.stage_finrank _ _ _ m
lemma fieldFlag_dimensions :
    Module.finrank F (fieldFlag 1).toSubmodule = 45 ∧
    Module.finrank F (fieldFlag 2).toSubmodule = 51 ∧
    Module.finrank F (fieldFlag 3).toSubmodule = 66 :=
  ⟨fieldFlag_finrank 1, fieldFlag_finrank 2, fieldFlag_finrank 3⟩
/-- Each stage is the ordinary field span of the indicated saved columns. -/
lemma fieldFlag_eq_span_columns (m : ℕ) :
    (fieldFlag m).toSubmodule = Submodule.span F (Set.range fun x : Fin (FieldFlag.cut m) =>
      flatten.symm (fun i => basisMatrix i (Fin.castLE (FieldFlag.cut_le m) x))) := by
  change FieldFlag.space FieldFlag.basisCoordinates m = _
  rw [FieldFlag.space_eq_span]
  apply congrArg (Submodule.span F)
  apply congrArg Set.range
  funext x
  apply flatten.injective
  rw [FieldFlag.flatten_basisCoordinates_symm, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_single_one]
  rfl
/-- Actual coordinate equivalences on the literal successive quotients. -/
def fieldFactorCoordinates (t : Fin 3) :
    ((fieldFlag (t.val+1)).toSubmodule ⧸
      (within (fieldFlag t.val) (fieldFlag (t.val+1))).toSubmodule) ≃ₗ[F]
        (Fin (factorDimension t) → F) :=
  FieldFlag.coordinates _ FieldFlag.basisCoordinates_generator FieldFlag.upper t
lemma fieldFactorCoordinates_generator (t : Fin 3) (a : Fin 2) v :
    fieldFactorCoordinates t
      ((within (fieldFlag t.val) (fieldFlag (t.val+1))).quotientRepresentation
        (ambientGenerator a) v) =
      (factorMatrix t a).mulVec (fieldFactorCoordinates t v) :=
  FieldFlag.coordinates_generator _ _ _ t a v
lemma fieldFactor_finrank (t : Fin 3) :
    Module.finrank F ((fieldFlag (t.val+1)).toSubmodule ⧸
      (within (fieldFlag t.val) (fieldFlag (t.val+1))).toSubmodule) = factorDimension t := by
  rw [(fieldFactorCoordinates t).finrank_eq, Module.finrank_fin_fun]

/-- The independently supplied full matrix algebras make the three literal
successive quotients simple. Their dimensions are 45, 6 and 15 over F₄. -/
theorem field_factorDegreeFiltration_of_matrix_algebras
    (hspan : ∀ (k : Fin 3)
      (Q : Subalgebra F (Matrix (Fin (factorDimension k)) (Fin (factorDimension k)) F)),
      factorMatrix k 0 ∈ Q → factorMatrix k 1 ∈ Q → Q = ⊤) :
    Representation.FactorDegreeFiltration ({6,15,45} : Set ℕ) (fieldRepresentation .dual) := by
  apply filtration_of_flag _ 3 fieldFlag fieldFlag_zero fieldFlag_last fieldFlag_mono
  · intro m hm
    let t : Fin 3 := ⟨m,hm⟩
    apply irreducible_of_coordinate_matrices (g := ambientGenerator)
      (A := factorMatrix t) (e := fieldFactorCoordinates t)
    · exact (by decide : ∀ k : Fin 3, 0 < factorDimension k) t
    · exact fieldFactorCoordinates_generator t
    · intro Q hQ
      exact hspan t Q (hQ 0) (hQ 1)
  · intro m hm
    rw [fieldFactor_finrank ⟨m,hm⟩]
    have h : ∀ t : Fin 3, factorDimension t ∈ ({6,15,45} : Set ℕ) := by decide
    exact h ⟨m,hm⟩
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
