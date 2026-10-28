module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms

/-!
# Assembly of the outer SL₃ adjoint calculation

Single-adjoint words descend to the actual binary adjoint representation.
The graph/root coordinate calculation gives the strict common-fixed-space
inequality, including the two smallest fields. Actual projective lifts give
the Schur-linear involution operator forms, and simultaneous reduction inside
the graph centralizer supplies one coordinate system for the whole actor.
The resulting `adjoint_estimate` discharges both structural inputs, allowing
the central kernel of the original SL₃ action.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The actual binary adjoint descent and common-fixed-space calculation
leave only the two independent structural normal-form obligations. -/
theorem adjoint_estimate_of_forms (hi : Adjoint.InvolutionForms B σ)
    (hg : Adjoint.GraphForms B σ) : SchurLinearAdjointEstimate B σ := by
  intro M hM A hA _ _ houter hschur
  obtain ⟨e⟩ := Adjoint.single_adjoint_binary_model B σ M hM
  obtain ⟨C⟩ := hg e A hA houter (by
    intro t ht
    let : IsElementaryAbelian 2 A := hA.2
    exact hi e t (elemPow_eq_one_of_isElementaryAbelian t ht) (hschur t ht))
  exact C.estimate

/-- The single-adjoint word admits no Schur-linear elementary outer actor
with cubic ratio at most two. The conclusion uses the literal common fixed
space, includes binary degrees one and two, and allows a central SL₃ kernel.
This discharges the adjoint branch of
`outer_word_estimate_of_schurLinear_branches`. -/
theorem adjoint_estimate (hk : σ.ker ≤ Subgroup.center _) :
    SchurLinearAdjointEstimate B σ :=
  adjoint_estimate_of_forms B σ (Adjoint.involution_forms B σ hk)
    (Adjoint.graph_forms B σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
