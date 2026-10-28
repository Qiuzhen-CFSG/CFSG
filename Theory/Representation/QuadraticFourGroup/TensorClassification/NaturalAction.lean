module

public import Theory.Representation.QuadraticFourGroup.Models
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RepresentationTheory.Character

/-!
# Natural actions for the quadratic four-group tensor classification

In characteristic two the center of SL₂ is trivial, so its actual quotient
PSL₂ acts faithfully on the two-dimensional coordinate space. Coefficient
embeddings and Frobenius powers give explicit natural actions, whose character
values range over the embedded matrix field. An explicit order-three matrix
fixes the cubic test element without any assumption on the field degree.

These constructions provide the concrete factors in GLS2, Theorem 25.14,
Step 5 and the remarks following its statement (ChapterG.tex, §§25.14).
They do not assert the irreducible-module classification or finite-field descent.
-/

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix
namespace Representation.QuadraticFourGroup.TensorClassification

theorem center_specialLinear_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center SL(2,K) = ⊥ := by
  apply (Subgroup.center SL(2,K)).eq_bot_iff_forall.mpr
  intro g hg
  obtain ⟨a, ha, h⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp ha with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  simpa [ha1] using h.symm

/-- The canonical central quotient map is an isomorphism in characteristic two. -/
noncomputable def specialLinearEquivFactor (n : ℕ) :
    SL(2, GaloisField 2 n) ≃* Factor n :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(2, GaloisField 2 n)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [QuotientGroup.ker_mk', center_specialLinear_eq_bot]),
      QuotientGroup.mk'_surjective _⟩

theorem specialLinearEquivFactor_apply (n : ℕ) (g : SL(2, GaloisField 2 n)) :
    specialLinearEquivFactor n g = QuotientGroup.mk' (Subgroup.center _) g := rfl

/-- The literal matrix action after applying a coefficient embedding. -/
noncomputable def naturalAction {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) : Representation F (Factor n) (Fin 2 → F) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (Matrix.SpecialLinearGroup.toLin'.comp
      ((Matrix.SpecialLinearGroup.map e).comp (specialLinearEquivFactor n).symm.toMonoidHom))

theorem naturalAction_injective {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) : Function.Injective (naturalAction e) := by
  intro g h heq
  apply (specialLinearEquivFactor n).symm.injective
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply e.injective
  have hm : (Matrix.SpecialLinearGroup.map e) ((specialLinearEquivFactor n).symm g) =
      (Matrix.SpecialLinearGroup.map e) ((specialLinearEquivFactor n).symm h) := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    exact heq
  exact congrArg (fun A : SL(2,F) => A i j) hm

theorem naturalAction_character {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) (g : Factor n) :
    (naturalAction e).character g =
      e (Matrix.trace ((specialLinearEquivFactor n).symm g : Matrix (Fin 2) (Fin 2) _) ) := by
  change LinearMap.trace F (Fin 2 → F)
    (Matrix.toLin' ((Matrix.SpecialLinearGroup.map e)
      ((specialLinearEquivFactor n).symm g) : Matrix (Fin 2) (Fin 2) F)) = _
  rw [Matrix.trace_toLin'_eq, Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
  rfl

/-- Traces recover the entire embedded matrix field, a common-field descent input. -/
theorem naturalAction_character_range {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) :
    Set.range (naturalAction e).character = Set.range e := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, (naturalAction_character e g).symm⟩
  · rintro _ ⟨a, rfl⟩
    let g : SL(2, GaloisField 2 n) := ⟨!![a, -1; 1, 0], by simp⟩
    refine ⟨specialLinearEquivFactor n g, ?_⟩
    rw [naturalAction_character, MulEquiv.symm_apply_apply]
    simp [g, Matrix.trace_fin_two]

/-- A natural module over the matrix field, twisted by the indicated Frobenius power. -/
noncomputable def frobeniusNatural (n i : ℕ) :
    Representation (GaloisField 2 n) (Factor n) (NaturalSpace n) :=
  naturalAction (iterateFrobeniusEquiv (GaloisField 2 n) 2 i).toRingHom

/-- The same Frobenius twist written on coordinates over a larger coefficient field. -/
noncomputable def mappedFrobeniusNatural {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) (i : ℕ) :
    Representation F (Factor n) (Fin 2 → F) :=
  naturalAction (e.comp (iterateFrobeniusEquiv (GaloisField 2 n) 2 i).toRingHom)

theorem frobeniusNatural_injective (n i : ℕ) :
    Function.Injective (frobeniusNatural n i) := naturalAction_injective _

theorem mappedFrobeniusNatural_character_range {n : ℕ} {F : Type*} [Field F]
    (e : GaloisField 2 n →+* F) (i : ℕ) :
    Set.range (mappedFrobeniusNatural e i).character = Set.range e := by
  rw [mappedFrobeniusNatural, naturalAction_character_range]
  change Set.range (e ∘ (iterateFrobeniusEquiv (GaloisField 2 n) 2 i)) = _
  rw [Set.range_comp, (iterateFrobeniusEquiv (GaloisField 2 n) 2 i).surjective.range_eq,
    Set.image_univ]

/-- The companion matrix for the polynomial `X² + X + 1`. -/
def cubicMatrix (K : Type*) [Field K] : SL(2,K) :=
  ⟨!![0, -1; 1, -1], by simp⟩

theorem cubicMatrix_order (K : Type*) [Field K] : orderOf (cubicMatrix K) = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cubicMatrix, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrArg (fun A : SL(2, K) => A 0 0) h
    exact zero_ne_one this

/-- A specified order-three element of the genuine projective group. -/
noncomputable def cubicElement (n : ℕ) : Factor n :=
  specialLinearEquivFactor n (cubicMatrix (GaloisField 2 n))

theorem cubicElement_order (n : ℕ) : orderOf (cubicElement n) = 3 := by
  exact ((specialLinearEquivFactor n).orderOf_eq _).trans (cubicMatrix_order _)

end Representation.QuadraticFourGroup.TensorClassification

end
