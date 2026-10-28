module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.ZeroDifferential

/-!
# Frobenius on the actual closed G₂ centralizer

The native coefficient Frobenius is bijective because scalar Frobenius on the
algebraic closure is an automorphism. Its restriction to a rational element's
centralizer remains surjective. Transport through `centralizerPointEquiv`
realizes this restriction as a regular morphism: every matrix coordinate,
including the inverse determinant coordinate, is raised to `Nat.card F`.

Differentiating these powers gives zero, since the field cardinality is zero
in the algebraic closure. Coordinate functions determine derivations, so this
proves vanishing of the entire identity differential. This supplies the actual
model inputs for the proved zero-differential Lang theorem. Connectedness of
the centralizer is a separate geometric obligation.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 10.7--10.8 and 12.5;
GLS III, Section 2.1 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.Bor1
open Atlas.SplitOctonion
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
open FieldExtension
noncomputable section
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K]

theorem coordinateMatrix_injective : Function.Injective (coordinateMatrix (F := K)) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [← coordinateMatrix_action, ← coordinateMatrix_action, he]

theorem fieldEmbedding_surjective (f : K ≃+* K) :
    Function.Surjective (fieldEmbedding f.toRingHom) := by
  intro z
  refine ⟨fieldEmbedding f.symm.toRingHom z, ?_⟩
  apply coordinateMatrix_injective
  apply Units.ext
  ext i j
  rw [fieldEmbedding_entry, fieldEmbedding_entry]
  exact f.apply_symm_apply _

variable (F : Type*) [Field F] [Finite F]
local notation "K₀" => AlgebraicClosure F

theorem frobenius_bijective : Function.Bijective (frobenius F) := by
  let := Fintype.ofFinite F
  refine ⟨fieldEmbedding_injective _, ?_⟩
  exact fieldEmbedding_surjective
    (FiniteField.frobeniusAlgEquivOfAlgebraic F K₀).toRingEquiv

def centralizerFrobenius (g : Model F) :
    Subgroup.centralizer ({fieldEmbedding (algebraMap F K₀) g} : Set (Model K₀)) →*
      Subgroup.centralizer ({fieldEmbedding (algebraMap F K₀) g} : Set (Model K₀)) where
  toFun z := ⟨frobenius F z.val, by
    rw [Subgroup.mem_centralizer_singleton_iff] at *
    simpa only [map_mul, frobenius_embedding] using congrArg (frobenius F)
      (Subgroup.mem_centralizer_singleton_iff.mp z.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem centralizerFrobenius_surjective (g : Model F) :
    Function.Surjective (centralizerFrobenius F g) := by
  intro z
  obtain ⟨u, hu⟩ := (frobenius_bijective F).surjective z.val
  have hc : u ∈ Subgroup.centralizer {fieldEmbedding (algebraMap F K₀) g} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply (frobenius_bijective F).injective
    simpa only [map_mul, frobenius_embedding, hu] using
      Subgroup.mem_centralizer_singleton_iff.mp z.property
  exact ⟨⟨u,hc⟩, Subtype.ext hu⟩

def centralizerPointFrobenius (g : Model F) :
    Variety.Point (centralizerVariety (fieldEmbedding (algebraMap F K₀) g)) →*
      Variety.Point (centralizerVariety (fieldEmbedding (algebraMap F K₀) g)) :=
  (centralizerPointEquiv _).symm.toMonoidHom.comp
    ((centralizerFrobenius F g).comp (centralizerPointEquiv _).toMonoidHom)

theorem centralizerPointFrobenius_apply (g : Model F)
    (p : Variety.Point (centralizerVariety (fieldEmbedding (algebraMap F K₀) g))) :
    (centralizerPointEquiv _ (centralizerPointFrobenius F g p)).val =
      frobenius F (centralizerPointEquiv _ p).val := by
  exact congrArg Subtype.val ((centralizerPointEquiv _).apply_symm_apply _)

theorem centralizerPointFrobenius_coordinates (g : Model F)
    (p : Variety.Point (centralizerVariety (fieldEmbedding (algebraMap F K₀) g)))
    (i : glCoordinates 8) :
    (centralizerPointFrobenius F g p).val i = p.val i ^ Nat.card F := by
  rcases i with ⟨i,j⟩ | ⟨⟩
  · rw [← centralizerPointEquiv_entry, centralizerPointFrobenius_apply,
      frobenius_entry, centralizerPointEquiv_entry]
  · rw [centralizerPointEquiv_scalar, centralizerPointEquiv_scalar,
      centralizerPointFrobenius_apply]
    let := Fintype.ofFinite F
    let f := (FiniteField.frobeniusAlgHom F K₀).toRingHom
    have hm : (coordinateMatrix (frobenius F (centralizerPointEquiv _ p).val) :
        Matrix (Fin 8) (Fin 8) K₀) =
        (coordinateMatrix (centralizerPointEquiv _ p).val :
          Matrix (Fin 8) (Fin 8) K₀).map f := by
      ext i j
      exact fieldEmbedding_entry f _ i j
    rw [hm]
    change ((f.mapMatrix) _).det⁻¹ = _
    rw [← RingHom.map_det, ← map_inv₀]
    change (_ : K₀) ^ Fintype.card F = _
    rw [Nat.card_eq_fintype_card]

def centralizerFrobeniusMorphism (g : Model F) :
    Morphism (centralizerVariety (fieldEmbedding (algebraMap F K₀) g))
      (centralizerVariety (fieldEmbedding (algebraMap F K₀) g)) where
  toVariety :=
    { toFun := centralizerPointFrobenius F g
      regular := fun i => ⟨MvPolynomial.X i ^ Nat.card F, fun p => by
        rw [centralizerPointFrobenius_coordinates]
        simp [evalPolynomial]⟩ }
  map_one := map_one _
  map_mul := map_mul _

theorem centralizerFrobeniusMorphism_surjective (g : Model F) :
    Function.Surjective (centralizerFrobeniusMorphism F g).onPoints :=
  (centralizerPointEquiv _).symm.surjective.comp
    ((centralizerFrobenius_surjective F g).comp (centralizerPointEquiv _).surjective)

private theorem differential_eq_zero_of_coordinates_pow
    {k : Type*} [Field k] [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G]
    (σ : Morphism G G) (q : ℕ) (hq : (q : k) = 0)
    (hc : ∀ x i, (σ.onPoints x).val i = x.val i ^ q) :
    identityTangentMorphismLinearMap σ = 0 := by
  apply LinearMap.ext
  intro D
  apply coordinateTangentMap_injective G
  funext i
  change D (σ.toVariety.pullbackAlgHom
    (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i))) = 0
  have hp : σ.toVariety.pullbackAlgHom
      (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)) =
      (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)) ^ q := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (σ.onPoints x).val (MvPolynomial.X i) =
      (evalPolynomial x.val (MvPolynomial.X i)) ^ q
    simpa only [evalPolynomial_X] using hc x i
  rw [hp, Derivation.leibniz_pow]
  simp only [nsmul_eq_mul, hq, zero_mul]

theorem centralizerFrobeniusMorphism_differential (g : Model F) :
    identityTangentMorphismLinearMap (centralizerFrobeniusMorphism F g) = 0 := by
  apply differential_eq_zero_of_coordinates_pow _ (Nat.card F) ?_
    (centralizerPointFrobenius_coordinates F g)
  let := Fintype.ofFinite F
  have h := congrArg (algebraMap F K₀) (FiniteField.cast_card_eq_zero (K := F))
  simpa only [map_natCast, map_zero, Nat.card_eq_fintype_card] using h

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
