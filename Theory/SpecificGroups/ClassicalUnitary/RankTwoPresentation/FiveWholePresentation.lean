module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelHomomorphisms
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveElimination

/-!
# The full special-unitary five-dimensional presentation

Two-column elimination proves that the faithful presentation evaluation
covers every SU₅ matrix. Its inverse and the universal property now construct
maps out of the entire special-unitary carrier, with the prescribed images
of all four positive groups, the full torus and both Weyl generators.
All finite parameters are retained, including the projective scalar center.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 33, using the
Bruhat presentation mechanism of Theorems 4 and 9.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePresentation
open FivePositive FiveWeyl
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
local notation "P" => parameters J
local notation "Gen" => Presentation.Generator (Multiplicative E) (Parameter J)
  (Multiplicative E) (Parameter J) (Eˣ × Eˣ)

theorem matrixGenerated_eq_top : matrixGenerated J κ hκ hJ=⊤ :=
  FiveElimination.fullGenerated_eq_top J κ hκ hJ

theorem evaluate_surjective : Function.Surjective (evaluate J κ hκ hJ) := by
  apply (P).evaluate_surjective (model_satisfies J κ hκ hJ)
  rw [model_roots,model_torus]
  exact FiveElimination.fullGenerated_eq_top J κ hκ hJ

/-- The explicit BC₂ relations present the WHOLE literal SU₅ group. -/
def equiv : (P).Carrier ≃* J.specialSubgroup :=
  MulEquiv.ofBijective (evaluate J κ hκ hJ)
    ⟨evaluate_injective J κ hκ hJ,evaluate_surjective J κ hκ hJ⟩

@[simp] theorem equiv_generator (j : Gen) :
    equiv J κ hκ hJ (PresentedGroup.of j)=modelGenerators J κ hκ hJ j :=
  (P).evaluate_generator (model_satisfies J κ hκ hJ) j

variable {Y : Type*} [Group Y]
/-- Construct a homomorphism on the entire SU₅ carrier from the explicit equations. -/
def lift {g : Gen → Y} (hg : (P).Satisfies g) : J.specialSubgroup →* Y :=
  ((P).evaluate hg).comp (equiv J κ hκ hJ).symm.toMonoidHom

@[simp] theorem lift_generator {g : Gen → Y} (hg : (P).Satisfies g) (j : Gen) :
    lift J κ hκ hJ hg (modelGenerators J κ hκ hJ j)=g j := by
  rw [←equiv_generator J κ hκ hJ j]
  change (P).evaluate hg ((equiv J κ hκ hJ).symm
    (equiv J κ hκ hJ (PresentedGroup.of j)))=g j
  rw [MulEquiv.symm_apply_apply,(P).evaluate_generator]

theorem lift_surjective {g : Gen → Y} (hg : (P).Satisfies g)
    (hgen : ReflectionLaws.fullGenerated hg.roots hg.torus (g .s) (g .t)=⊤) :
    Function.Surjective (lift J κ hκ hJ hg) :=
  ((P).evaluate_surjective hg hgen).comp (equiv J κ hκ hJ).symm.surjective
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePresentation
