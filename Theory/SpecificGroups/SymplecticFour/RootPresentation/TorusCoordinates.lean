module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.FiniteTorus
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.FinCases

/-!
# The two-dimensional C₂ coroot torus

The root-weight formulas and the internally proved multiplicativity show
that the two simple-coroot ranges commute. Their product is consequently
a homomorphism from F* × F*. Conjugating the two long roots separates its
two parameters: squaring is injective in characteristic two. Applying this
to the actual matrix roots proves that evaluation is faithful on the whole
simple-coroot torus of the presentation.

This proves the torus-kernel step of Steinberg's presentation argument;
placing the full presentation kernel in this torus still requires Bruhat
collection. Source: Steinberg §6, Lemmas 37–39 and Theorem 8(b), pp.70–73.
-/

@[expose] public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
variable {F E : Type*} [Field F] [Group E] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem opposite_weight (i j : Fin 2) (s : Fˣ) :
    simpleFactor i s (simpleReflection i (oppositeSimpleRoot j)) =
      (simpleFactor i s (simpleReflection i (simpleRoot j)))⁻¹ := by
  fin_cases i <;> fin_cases j <;>
    simp [simpleFactor, simpleReflection, oppositeSimpleRoot, simpleRoot, shortFactor, longFactor,
      shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

namespace Relations
variable {x : Fin 8 → F → E} (h : Relations x)
include h

private theorem torusWord_conj_otherWord (i j : Fin 2) (s t : Fˣ) :
    MulAut.conj (torusWord x i s) (simpleWord x j t) =
      simpleWord x j (t * simpleFactor i s (simpleReflection i (simpleRoot j))) := by
  simp only [simpleWord, map_mul, h.torusWord_conj, opposite_weight, Units.val_mul,
    mul_inv_rev, Units.val_inv_eq_inv_val]
  congr 2 <;> simp [mul_comm]

/-- The two simple-coroot ranges commute, after internal discharge of (C). -/
theorem torusWord_commute (i j : Fin 2) (s t : Fˣ) :
    Commute (torusWord x i s) (torusWord x j t) := by
  let c := simpleFactor i s (simpleReflection i (simpleRoot j))
  have he : MulAut.conj (torusWord x i s) (torusWord x j t) =
      torusWord x j (t*c) * (torusWord x j c)⁻¹ := by
    change MulAut.conj (torusWord x i s) (simpleWord x j t * simpleWord x j 1) = _
    rw [map_mul, h.torusWord_conj_otherWord, h.torusWord_conj_otherWord, one_mul]
    simp only [torusWord, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [h.simpleWord_inv]
  rw [← h.torusWord_mul, mul_inv_cancel_right] at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Both simple coroots together, with their literal parameters retained. -/
def torusPairHom : (Fˣ × Fˣ) →* E :=
  (h.torusHom 0).noncommCoprod (h.torusHom 1) (h.torusWord_commute 0 1)

@[simp] theorem torusPairHom_apply (s t : Fˣ) :
    h.torusPairHom (s,t) = torusWord x 0 s * torusWord x 1 t := rfl

theorem torusPairHom_range : h.torusPairHom.range =
    (h.torusHom 0).range ⊔ (h.torusHom 1).range := MonoidHom.noncommCoprod_range _ _ _

theorem torusPairHom_range_le_normalizer :
    h.torusPairHom.range ≤ normalizer (PositiveRelations.positiveSubgroup x) := by
  rw [h.torusPairHom_range]
  exact sup_le (h.torusHom_range_le_normalizer 0) (h.torusHom_range_le_normalizer 1)

private theorem torusPair_root_zero (s t : Fˣ) :
    MulAut.conj (h.torusPairHom (s,t)) (x 0 1) = x 0 ((s : F)^2) := by
  simp only [h.torusPairHom_apply, map_mul, MulAut.mul_apply, h.torusWord_conj]
  simp [simpleFactor, simpleReflection, shortFactor, longFactor, shortReflection,
    longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem torusPair_root_two (s t : Fˣ) :
    MulAut.conj (h.torusPairHom (s,t)) (x 2 1) = x 2 (((s : F)⁻¹)^2 * (t : F)^2) := by
  simp only [h.torusPairHom_apply, map_mul, MulAut.mul_apply, h.torusWord_conj]
  simp [simpleFactor, simpleReflection, shortFactor, longFactor, shortReflection,
    longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- The two long-root parameter maps separate the two independent coroots.
This needs neither global presentation faithfulness nor matrix diagonal reduction. -/
theorem torusPairHom_injective (h0 : Function.Injective (x 0)) (h2 : Function.Injective (x 2)) :
    Function.Injective h.torusPairHom := by
  rintro ⟨s,t⟩ ⟨u,v⟩ he
  have he0 := congrArg (fun g => MulAut.conj g (x 0 1)) he
  rw [h.torusPair_root_zero, h.torusPair_root_zero] at he0
  have hs : s = u := Units.ext (CharTwo.sq_injective (h0 he0))
  subst u
  have he2 := congrArg (fun g => MulAut.conj g (x 2 1)) he
  rw [h.torusPair_root_two, h.torusPair_root_two] at he2
  have ht : t = v := Units.ext (CharTwo.sq_injective
    (mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero (Units.ne_zero s))) (h2 he2)))
  exact Prod.ext rfl ht
end Relations

/-- Evaluation preserves the literal two-coroot parametrization. -/
theorem matrixMap_torusPairHom :
    matrixMap.comp (generator_relations.torusPairHom (F := F)) = matrix_relations.torusPairHom := by
  apply MonoidHom.ext
  rintro ⟨s,t⟩
  simp only [MonoidHom.comp_apply, Relations.torusPairHom_apply, torusWord, simpleWord,
    map_mul, matrixMap_generator]

/-- Matrix evaluation has trivial kernel on the full two-dimensional coroot torus. -/
theorem matrixMap_injective_on_torus : Set.InjOn (matrixMap (F := F))
    ((generator_relations.torusPairHom (F := F)).range : Set (SteinbergGroup F)) := by
  rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩ he
  have hpq : matrix_relations.torusPairHom p = matrix_relations.torusPairHom q := by
    simpa only [← matrixMap_torusPairHom, MonoidHom.comp_apply] using he
  exact congrArg generator_relations.torusPairHom
    (matrix_relations.torusPairHom_injective (RootSubgroup.element_injective 0)
      (RootSubgroup.element_injective 2) hpq)

end Theory.SpecificGroups.SymplecticFour.RootPresentation
