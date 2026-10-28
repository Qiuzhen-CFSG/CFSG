module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.WeylParameters
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Finite-field C₂ coroot multiplicativity

The proved Weyl formulas determine conjugation by both simple coroot words
on all eight root groups. Their conjugation actions are multiplicative.
Cyclicity of the finite field's unit group then makes the coroot words on
each fixed root commute. The square-scaling identity proves relation (C),
since squaring is bijective in a finite field of characteristic two.
No global kernel theorem, Bruhat theorem, or model simplicity is assumed.

The two resulting homomorphisms normalize the full positive subgroup,
which supplies their placement in the full marked source Borel.

Source: Steinberg §6, Lemma 37(f), Lemma 39(b,c), Theorem 9, pp.70–74.
The cyclicity argument follows the checked project proof in
`PSL3/UniversalProjection/Faithfulness/FiniteTorus.lean`, specialized here
to the literal C₂ words and to characteristic two.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation

def simpleRoot : Fin 2 → Fin 8 := ![6,2]
def oppositeSimpleRoot : Fin 2 → Fin 8 := ![7,3]
def simpleReflection : Fin 2 → Equiv.Perm (Fin 8) := ![shortReflection,longReflection]

variable {F E : Type*} [Field F] [Group E]

def simpleWord (x : Fin 8 → F → E) (i : Fin 2) (t : Fˣ) : E :=
  x (simpleRoot i) t * x (oppositeSimpleRoot i) ((t⁻¹ : Fˣ) : F) * x (simpleRoot i) t

def simpleFactor (i : Fin 2) (t : Fˣ) : Fin 8 → Fˣ := ![shortFactor t,longFactor t] i

/-- The literal coroot word, with no multiplicative relation imposed. -/
def torusWord (x : Fin 8 → F → E) (i : Fin 2) (t : Fˣ) : E :=
  simpleWord x i t * simpleWord x i 1

private theorem reflection_twice (i : Fin 2) (r : Fin 8) :
    simpleReflection i (simpleReflection i r) = r := by
  fin_cases i <;> fin_cases r <;> decide

private theorem simpleFactor_one (i : Fin 2) (r : Fin 8) : simpleFactor i (1 : Fˣ) r = 1 := by
  fin_cases i <;> fin_cases r <;> simp [simpleFactor, shortFactor, longFactor]

private theorem simpleFactor_mul (i : Fin 2) (s t : Fˣ) (r : Fin 8) :
    simpleFactor i (s*t) r = simpleFactor i s r * simpleFactor i t r := by
  fin_cases i <;> fin_cases r <;>
    simp [simpleFactor, shortFactor, longFactor, mul_pow, mul_inv_rev, mul_comm]

private theorem factor_reflected_simple (i : Fin 2) (t : Fˣ) :
    simpleFactor i t (simpleReflection i (simpleRoot i)) = t^2 := by
  fin_cases i <;> simp [simpleFactor, simpleReflection, simpleRoot, shortFactor, longFactor,
    shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem factor_reflected_opposite (i : Fin 2) (t : Fˣ) :
    simpleFactor i t (simpleReflection i (oppositeSimpleRoot i)) = (t⁻¹)^2 := by
  fin_cases i <;> simp [simpleFactor, simpleReflection, oppositeSimpleRoot, shortFactor, longFactor,
    shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

variable [Finite F] [CharP F 2]

namespace Relations
variable {x : Fin 8 → F → E} (h : Relations x)
include h

theorem simpleWord_conj (i : Fin 2) (t : Fˣ) (r : Fin 8) (u : F) :
    MulAut.conj (simpleWord x i t) (x r u) =
      x (simpleReflection i r) ((simpleFactor i t r : F) * u) := by
  fin_cases i
  · simpa [simpleWord, shortWord, simpleRoot, oppositeSimpleRoot, simpleReflection, simpleFactor, mul_assoc] using h.shortWord_conj t r u
  · simpa [simpleWord, longWord, simpleRoot, oppositeSimpleRoot, simpleReflection, simpleFactor, mul_assoc] using h.longWord_conj t r u

omit [Finite F] in
theorem simpleWord_inv (i : Fin 2) (t : Fˣ) : (simpleWord x i t)⁻¹ = simpleWord x i t := by
  simp only [simpleWord, mul_inv_rev, h.positive.inv, mul_assoc]

omit [Finite F] in
theorem torusWord_one (i : Fin 2) : torusWord x i 1 = 1 := by
  change simpleWord x i 1 * simpleWord x i 1 = 1
  simpa only [h.simpleWord_inv] using inv_mul_cancel (simpleWord x i 1)

/-- The coroot acts by the explicit root weights on all eight additive groups. -/
theorem torusWord_conj (i : Fin 2) (t : Fˣ) (r : Fin 8) (u : F) :
    MulAut.conj (torusWord x i t) (x r u) =
      x r ((simpleFactor i t (simpleReflection i r) : F) * u) := by
  simp only [torusWord, map_mul, MulAut.mul_apply, h.simpleWord_conj,
    simpleFactor_one, Units.val_one, one_mul, reflection_twice]

theorem torusWord_conj_simpleWord (i : Fin 2) (s t : Fˣ) :
    MulAut.conj (torusWord x i s) (simpleWord x i t) = simpleWord x i (t*s^2) := by
  simp only [simpleWord, map_mul, h.torusWord_conj, factor_reflected_simple,
    factor_reflected_opposite, Units.val_pow_eq_pow_val, Units.val_mul,
    mul_inv_rev, Units.val_inv_eq_inv_val]
  congr 2 <;> simp [mul_comm]

/-- Steinberg Lemma 37(f), with the corrected literal parameter placement. -/
theorem torusWord_conj_torusWord (i : Fin 2) (s t : Fˣ) :
    MulAut.conj (torusWord x i s) (torusWord x i t) =
      torusWord x i (t*s^2) * (torusWord x i (s^2))⁻¹ := by
  change MulAut.conj (torusWord x i s) (simpleWord x i t * simpleWord x i 1) = _
  rw [map_mul, h.torusWord_conj_simpleWord, h.torusWord_conj_simpleWord, one_mul]
  simp only [torusWord, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  rw [h.simpleWord_inv]

end Relations

private def torusConjugation (i : Fin 2) : Fˣ →* MulAut (SteinbergGroup F) where
  toFun t := MulAut.conj (torusWord generator i t)
  map_one' := by rw [generator_relations.torusWord_one, map_one]
  map_mul' s t := by
    apply MulEquiv.toMonoidHom_injective
    apply PresentedGroup.ext
    rintro ⟨r,u⟩
    change MulAut.conj (torusWord generator i (s*t)) (generator r u) =
      MulAut.conj (torusWord generator i s) (MulAut.conj (torusWord generator i t) (generator r u))
    simp only [generator_relations.torusWord_conj, simpleFactor_mul, Units.val_mul, mul_assoc]

/-- Cyclicity of F* makes the torus words on either fixed root commute.
This is proved before any Bruhat or global kernel theorem. -/
private theorem generator_torus_commute (i : Fin 2) (s t : Fˣ) :
    Commute (torusWord generator i s) (torusWord generator i t) := by
  let h := torusWord (generator (F := F)) i
  let φ := torusConjugation (F := F) i
  obtain ⟨v,hv⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨m,hm⟩ := hv s
  obtain ⟨n,hn⟩ := hv t
  have he (k : ℤ) : MulAut.conj (h (v^k)) = MulAut.conj (h v ^ k) := by
    change φ (v^k) = MulAut.conj (h v ^ k)
    rw [map_zpow, map_zpow]
    rfl
  have hc (k : ℤ) : Commute (h (v^k)) (h v) := by
    have he' := congrArg (fun f : MulAut (SteinbergGroup F) => f (h v)) (he k)
    simp only [MulAut.conj_apply] at he'
    rw [(Commute.refl (h v)).zpow_left k |>.eq] at he'
    simp only [mul_inv_cancel_right] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  change Commute (h s) (h t)
  rw [← hm, ← hn]
  have he' := congrArg (fun f : MulAut (SteinbergGroup F) => f (h (v^m))) (he n)
  simp only [MulAut.conj_apply] at he'
  rw [((hc m).symm.zpow_left n).eq] at he'
  simp only [mul_inv_cancel_right] at he'
  exact (show Commute (h (v^n)) (h (v^m)) from mul_inv_eq_iff_eq_mul.mp he').symm

private theorem unit_square_surjective : Function.Surjective (fun t : Fˣ => t^2) := by
  apply Finite.surjective_of_injective
  intro s t he
  apply Units.ext
  apply CharTwo.sq_injective
  exact congrArg (fun u : Fˣ => (u : F)) he

/-- Relation (C) follows internally from (A) and (B) over every finite
characteristic-two field. It is not an additional source assumption. -/
theorem Relations.torusWord_mul {x : Fin 8 → F → E} (h : Relations x)
    (i : Fin 2) (s t : Fˣ) : torusWord x i s * torusWord x i t = torusWord x i (s*t) := by
  suffices he : torusWord generator i s * torusWord generator i t =
      torusWord generator i (s*t) by
    simpa only [torusWord, simpleWord, map_mul, lift_generator] using congrArg (lift h) he
  obtain ⟨u,rfl⟩ := unit_square_surjective (F := F) t
  have he := generator_relations.torusWord_conj_torusWord i u s
  rw [MulAut.conj_apply, (generator_torus_commute i u s).eq,
    mul_assoc, mul_inv_cancel, mul_one] at he
  exact eq_mul_inv_iff_mul_eq.mp he

/-- The two literal simple-coroot words are homomorphisms, with no symbol kernel. -/
def Relations.torusHom {x : Fin 8 → F → E} (h : Relations x) (i : Fin 2) : Fˣ →* E where
  toFun := torusWord x i
  map_one' := h.torusWord_one i
  map_mul' s t := (h.torusWord_mul i s t).symm


/-- Both coroot ranges normalize the full positive subgroup. -/
theorem Relations.torusHom_range_le_normalizer {x : Fin 8 → F → E} (h : Relations x)
    (i : Fin 2) : (h.torusHom i).range ≤ normalizer (PositiveRelations.positiveSubgroup x) := by
  apply le_normalizer_closure_iff.mpr
  rintro _ ⟨t,rfl⟩ _ ⟨r,hr,u,rfl⟩
  change MulAut.conj (torusWord x i t) (x r u) ∈ PositiveRelations.positiveSubgroup x
  rw [h.torusWord_conj]
  exact root_mem_span _ hr _

end Theory.SpecificGroups.SymplecticFour.RootPresentation
