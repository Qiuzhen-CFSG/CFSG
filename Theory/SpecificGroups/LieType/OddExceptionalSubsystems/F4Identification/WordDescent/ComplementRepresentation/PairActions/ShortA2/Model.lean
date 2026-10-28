module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The shared marked SL3 model for the short A2 comparison

The first node uses the elementary matrices x01(t), x10(t), and the second
uses x12(t), x21(t). True selects the first node and the positive sign. Their
commutators give x02(t) and x20(t), so elementary generation proves that the
four curves generate the whole special linear group over every field.

These definitions fix a common domain for the independent F4 and E6 matrix
comparisons. They assert no identification of either subsystem. `DiagonalModel`
uses generation to restrict a marked E6 homomorphism to the actual end chain.
Source: the common-lattice subsystem construction of GLS3 §2.6.2, used in
Aschbacher--Smith A.2.17, printed p.39.

The elementary generation and commutator APIs are reused from the attributed
ATLAS port `Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`; its
attribution and license remain there and in `LICENSES/ATLAS.txt`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open Matrix
open scoped commutatorElement

variable (F : Type*) [Field F]

/-- The full SL3 matrix group, before taking any central quotient. -/
abbrev Model := Matrix.SpecialLinearGroup (Fin 3) F

/-- The common signed marking for the two independent matrix comparisons. -/
def modelGenerator (s k : Bool) (t : F) : Model F :=
  if k then
    if s then SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t
    else SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t
  else
    if s then SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t
    else SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t

@[simp] theorem modelGenerator_zero (s k : Bool) : modelGenerator F s k 0 = 1 := by
  cases s <;> cases k <;> exact SpecialLinearGroup.transvection_coeff_zero (by decide)

theorem modelGenerator_add (s k : Bool) (t u : F) :
    modelGenerator F s k (t + u) = modelGenerator F s k t * modelGenerator F s k u := by
  cases s <;> cases k <;> exact SpecialLinearGroup.transvection_add (by decide) _ _

/-- The four adjacent signed elementary curves generate SL3. -/
theorem model_generates (H : Subgroup (Model F))
    (h : ∀ (s k : Bool) (t : F), modelGenerator F s k t ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun a => a ∈ H) _ (fun _ _ => H.mul_mem) g
  intro i j hij t
  have hcomm {a b : Model F} (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h true true t
  · rw [← mul_one t, ← Atlas.elementary_commutator hij
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide) t 1]
    exact hcomm (h true true t) (h true false 1)
  · exact h false true t
  · exact (hij rfl).elim
  · exact h true false t
  · rw [← mul_one t, ← Atlas.elementary_commutator hij
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide) t 1]
    exact hcomm (h false false t) (h false true 1)
  · exact h false false t
  · exact (hij rfl).elim

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
