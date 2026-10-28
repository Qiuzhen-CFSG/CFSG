module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Input
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.TorusCoordinates
import Mathlib.Tactic.FinCases

/-!
# Weyl words and the full coroot torus on the marked C₂ quotient

The eight-root input initially places only the parameter-one negative
simple roots in the two marked parabolics. The proved Weyl conjugation
formulas place every negative-simple-root parameter, and hence every simple
Weyl word, in the same correctly oriented endpoints. Coroot conjugation
normalizes the positive subgroup. The split quotient's normalizer theorem
therefore places the full two-parameter coroot homomorphism in the actual
Borel, without an extra Cartan-matching assumption.

These conclusions concern the same X/Q.D even if X is infinite. They do
not assert global presentation faithfulness or a symplectic recognition.
Source: DGS Theorem D, printed p.224; Steinberg §6, pp.69–74.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour.RootPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
variable {X F : Type*} [Group X] [Field F]
variable {P : Fin 2 → Subgroup X} {Q : MarkedQuotient P} {split : SplitData Q.tits}
namespace RootData
variable (d : RootData (F := F) Q split)

theorem positive_root_mem (r : Fin 8) (hr : r ∈ ({6,0,4,2} : Set (Fin 8))) (t : F) :
    d.x r (.ofAdd t) ∈ split.U := by
  rw [← d.positive]
  exact root_mem_span _ hr t

private theorem positive_parabolic (r : Fin 8) (hr : r ∈ ({6,0,4,2} : Set (Fin 8)))
    (t : F) (i : Fin 2) : d.x r (.ofAdd t) ∈ Q.tits.standardParabolic {Q.simple i} :=
  Q.tits.B_le_standardParabolic _ (split.U_le (d.positive_root_mem r hr t))

variable [Finite F] [CharP F 2]

/-- All parameters of the negative long root lie in the first marked endpoint.
The input only placed parameter one there. -/
theorem negative_long_all (t : F) :
    d.x 3 (.ofAdd t) ∈ Q.tits.standardParabolic {Q.simple 0} := by
  let x := fun r u => d.x r (.ofAdd u)
  have hw : longWord x 1 ∈ Q.tits.standardParabolic {Q.simple 0} :=
    mul_mem (mul_mem (d.positive_parabolic 2 (by simp) 1 0) (by simpa [x] using d.negative_long))
      (d.positive_parabolic 2 (by simp) 1 0)
  have he : longWord x 1 * x 2 t * (longWord x 1)⁻¹ = x 3 t :=
    d.relations.longWord_one_conj 2 t
  change x 3 t ∈ Q.tits.standardParabolic {Q.simple 0}
  rw [← he]
  exact mul_mem (mul_mem hw (d.positive_parabolic 2 (by simp) t 0)) (inv_mem hw)

/-- All parameters of the negative short root lie in the second marked endpoint. -/
theorem negative_short_all (t : F) :
    d.x 7 (.ofAdd t) ∈ Q.tits.standardParabolic {Q.simple 1} := by
  let x := fun r u => d.x r (.ofAdd u)
  have hw : shortWord x 1 ∈ Q.tits.standardParabolic {Q.simple 1} :=
    mul_mem (mul_mem (d.positive_parabolic 6 (by simp) 1 1) (by simpa [x] using d.negative_short))
      (d.positive_parabolic 6 (by simp) 1 1)
  have he : shortWord x 1 * x 6 t * (shortWord x 1)⁻¹ = x 7 t :=
    d.relations.shortWord_one_conj 6 t
  change x 7 t ∈ Q.tits.standardParabolic {Q.simple 1}
  rw [← he]
  exact mul_mem (mul_mem hw (d.positive_parabolic 6 (by simp) t 1)) (inv_mem hw)

/-- Root index zero is short (source endpoint one); root index one is long
(source endpoint zero). This keeps the original orientation explicit. -/
def weylWord (i : Fin 2) (t : Fˣ) : X ⧸ Q.D :=
  simpleWord (fun r u => d.x r (.ofAdd u)) i t

theorem weylWord_mem (i : Fin 2) (t : Fˣ) :
    d.weylWord i t ∈ Q.tits.standardParabolic {Q.simple (![1,0] i)} := by
  fin_cases i
  · exact mul_mem (mul_mem (d.positive_parabolic 6 (by simp) t 1)
      (d.negative_short_all ((t⁻¹ : Fˣ) : F))) (d.positive_parabolic 6 (by simp) t 1)
  · exact mul_mem (mul_mem (d.positive_parabolic 2 (by simp) t 0)
      (d.negative_long_all ((t⁻¹ : Fˣ) : F))) (d.positive_parabolic 2 (by simp) t 0)

/-- Weyl action on the original eight maps on the SAME finite quotient. -/
theorem weylWord_conj (i : Fin 2) (t : Fˣ) (r : Fin 8) (u : F) :
    d.weylWord i t * d.x r (.ofAdd u) * (d.weylWord i t)⁻¹ =
      d.x (simpleReflection i r) (.ofAdd ((simpleFactor i t r : F)*u)) :=
  d.relations.simpleWord_conj i t r u

/-- The actual coroot homomorphism on the marked source quotient. -/
def corootHom (i : Fin 2) : Fˣ →* (X ⧸ Q.D) := d.relations.torusHom i

theorem corootHom_mem_borel (i : Fin 2) (t : Fˣ) : d.corootHom i t ∈ Q.tits.B := by
  rw [← split.normalizer_eq, ← d.positive]
  exact d.relations.torusHom_range_le_normalizer i ⟨t,rfl⟩

/-- Both coroot ranges land in the full Borel, including its odd part. -/
def borelCorootHom (i : Fin 2) : Fˣ →* Q.tits.B :=
  (d.corootHom i).codRestrict Q.tits.B (d.corootHom_mem_borel i)

@[simp] theorem borelCorootHom_coe (i : Fin 2) (t : Fˣ) :
    (d.borelCorootHom i t : X ⧸ Q.D) = d.corootHom i t := rfl

/-- The Borel-valued coroot retains its literal two Weyl words. -/
theorem corootHom_eq_word (i : Fin 2) (t : Fˣ) :
    d.corootHom i t = d.weylWord i t * d.weylWord i 1 := rfl


/-- The full two-parameter torus on the SAME source quotient. -/
def torusPairHom : (Fˣ × Fˣ) →* (X ⧸ Q.D) := d.relations.torusPairHom

theorem torusPairHom_mem_borel (p : Fˣ × Fˣ) : d.torusPairHom p ∈ Q.tits.B :=
  mul_mem (d.corootHom_mem_borel 0 p.1) (d.corootHom_mem_borel 1 p.2)

def borelTorusHom : (Fˣ × Fˣ) →* Q.tits.B :=
  d.torusPairHom.codRestrict Q.tits.B d.torusPairHom_mem_borel

@[simp] theorem borelTorusHom_coe (p : Fˣ × Fˣ) :
    (d.borelTorusHom p : X ⧸ Q.D) = d.torusPairHom p := rfl

theorem torusPairHom_eq_words (s t : Fˣ) :
    d.torusPairHom (s,t) = (d.weylWord 0 s * d.weylWord 0 1) *
      (d.weylWord 1 t * d.weylWord 1 1) := rfl

end RootData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
