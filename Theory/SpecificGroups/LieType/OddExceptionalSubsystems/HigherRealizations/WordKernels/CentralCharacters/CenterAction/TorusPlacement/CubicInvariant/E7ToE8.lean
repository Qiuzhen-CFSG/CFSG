module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks

/-!
# Restricting the literal E8 residue equation to its E7 adjoint block

The E7 roots form the saturated subsystem of E8 orthogonal to `e₀ + e₁`.
The root inclusion and the first seven simple nodes define an integral Geck
basis inclusion. The existing divided-power theorem for saturated based
subsystems intertwines all six signed curves and hence every six-node word,
over any field. The integral pairings also agree, so the balanced residue
diagonals have exactly the same entries on this included basis.

Consequently an E8 word equal to `residueDiagonal u` restricts to the E7 word
equal to `residueDiagonal u`. This is an actual matrix comparison; no abstract
identification of the two word images or central exponent is presumed. The
consumer in `CubicInvariant` reduces the E8 cubic constraint to the single
27-coordinate E7 block.

Source: the common-lattice subsystem construction of GLS3 §2.6.2
(`refs/KGroup/GLS3/chapter2.tex`), used in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7ToE8
open AdjointBlocks
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- The literal E7 roots, viewed as E8 roots. -/
def root : typeE7Roots ↪ typeE8Roots where
  toFun r := ⟨r.val, r.property.1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun r : typeE8Roots => r.val) h)

/-- The first seven simple nodes, with the repository’s numbering. -/
def base : typeE7RootPairing_base.support ↪ typeE8RootPairing_base.support where
  toFun i := typeE8RootPairing_baseEquiv
    ((typeE7RootPairing_baseEquiv.symm i).castLE (by decide))
  inj' _ _ h := typeE7RootPairing_baseEquiv.symm.injective
    (Fin.castLE_injective (by decide) (typeE8RootPairing_baseEquiv.injective h))

@[simp] theorem base_numbered (i : Fin 7) :
    base (typeE7RootPairing_baseEquiv i) =
      typeE8RootPairing_baseEquiv (i.castLE (by decide)) := by
  change typeE8RootPairing_baseEquiv
    ((typeE7RootPairing_baseEquiv.symm (typeE7RootPairing_baseEquiv i)).castLE (by decide)) = _
  rw [Equiv.symm_apply_apply]

/-- The E7 hyperplane is a saturated based root subsystem of E8. -/
def embedding : BasedEmbedding typeE7RootPairing_base typeE8RootPairing_base where
  index := root
  weight := typeE7Space.subtype
  injective := Subtype.val_injective
  root _ := rfl
  saturated x hx := by
    obtain ⟨r, hr⟩ := hx
    have hv : r.val = x.val := hr
    refine ⟨⟨x.val, hv ▸ r.property, x.property⟩, ?_⟩
    apply Subtype.ext
    rfl
  base := base
  base_root i := by
    obtain ⟨i, rfl⟩ := typeE7RootPairing_baseEquiv.surjective i
    change root (typeE7RootPairing_baseEquiv i) =
      (base (typeE7RootPairing_baseEquiv i) : typeE8Roots)
    rw [base_numbered]
    apply Subtype.ext
    rfl
  cartan i j := by
    obtain ⟨i, rfl⟩ := typeE7RootPairing_baseEquiv.surjective i
    obtain ⟨j, rfl⟩ := typeE7RootPairing_baseEquiv.surjective j
    rw [base_numbered, base_numbered,
      typeE8RootPairing_base_cartan_apply, typeE7RootPairing_base_cartan_apply]
    fin_cases i <;> fin_cases j <;> decide

@[simp] theorem embedding_base_numbered (i : Fin 7) :
    embedding.base (typeE7RootPairing_baseEquiv i) =
      typeE8RootPairing_baseEquiv (i.castLE (by decide)) := base_numbered i

@[simp] theorem base_node (i : Fin 6) : embedding.base (e7Node i) = e8Node i := by
  change base (typeE7RootPairing_baseEquiv _) = _
  rw [base_numbered]
  rfl

theorem pairing (r s : typeE7Roots) :
    typeE8RootPairing.pairingIn ℤ (root r) (root s) =
      typeE7RootPairing.pairingIn ℤ r s := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  simp only [RootPairing.algebraMap_pairingIn, typeE8RootPairing_pairing,
    typeE7RootPairing_pairing]
  rfl

theorem centralExponent_indexMap (a : typeE7RootPairing_base.support ⊕ typeE7Roots) :
    centralExponent e8Node (embedding.indexMap a) = centralExponent e7Node a := by
  have hw (r : typeE7Roots) (i : Fin 6) :
      typeE8RootPairing.pairingIn ℤ (root r) (e8Node i) =
        typeE7RootPairing.pairingIn ℤ r (e7Node i) := by
    rw [← base_node, ← embedding.base_root]
    exact pairing r (e7Node i)
  cases a <;> simp [centralExponent, chevalleyBasisWeight,
    BasedEmbedding.indexMap, embedding, hw]

variable (F : Type*) [Field F]

theorem simple_intertwines (s : Bool) (i : Fin 6) (t : F) :
    (e8Simple F s (i.castLE (by decide)) t).val.val *
      inclusionOver embedding.indexMap F =
    inclusionOver embedding.indexMap F *
      (e7Simple F s (i.castLE (by decide)) t).val.val := by
  rw [signedSimple_val, signedSimple_val]
  simp only [IntegralCubicFamily.unit_val]
  have h := embedding.curve_intertwines F s (e7Node i) t
  rw [base_node] at h
  exact h

theorem word_intertwines (w : SixNodeWord F) :
    (e8Six F w).val.val * inclusionOver embedding.indexMap F =
      inclusionOver embedding.indexMap F * (e7Six F w).val.val := by
  apply AdjointBlocks.word_intertwines ((Subgroup.subtype _).comp (e7Six F))
    ((Subgroup.subtype _).comp (e8Six F)) (inclusionOver embedding.indexMap F)
  rintro ⟨s, i, t⟩
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, e7Six_of, e8Six_of] using
    simple_intertwines F s i t

theorem residueDiagonal_intertwines (u : Fˣ) :
    (residueDiagonal F e8Node u).val * inclusionOver embedding.indexMap F =
      inclusionOver embedding.indexMap F * (residueDiagonal F e7Node u).val := by
  ext row col
  simp only [residueDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    inclusionOver_apply]
  by_cases h : row = embedding.indexMap col
  · subst row
    rw [centralExponent_indexMap]
    simp
  · simp [h]

/-- Equality to an E8 residue diagonal implies the same literal E7 equality. -/
theorem e7Six_eq_residueDiagonal_of_e8Six_eq (w : SixNodeWord F) (u : Fˣ)
    (h : (e8Six F w).val = residueDiagonal F e8Node u) :
    (e7Six F w).val = residueDiagonal F e7Node u := by
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  apply inclusion_mulVec_injective embedding.indexMap F
  rw [Matrix.mulVec_mulVec, ← word_intertwines, h, residueDiagonal_intertwines,
    ← Matrix.mulVec_mulVec]

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.E7ToE8
