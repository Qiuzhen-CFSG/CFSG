module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison

/-!
# Applying the odd minus-six exterior comparison to a simple ambient group

The ambient isomorphism supplies simplicity of the original PΩ⁻₆ carrier.
The completed signed exterior comparison then yields an actual PSU₄ model
over the field of order q² with conjugation x ↦ x^q. No geometric realization,
commutator, normality or model-simplicity premise remains in the model-predicate
implication. The field witness itself supplies the prime-power parameter.

This discharges the minus-six alias used in the orthogonal dimension reduction
of Aschbacher–Smith A.2.17, printed pp.38–39; see GLS3 §2.7. The parent retains
the full dimension-reduction assembly. The earlier conditional consumer is
preserved for applications with a supplied exterior realization.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
open ClassicalGroup ClassicalOrthogonal.Minus.OddSixComparison

universe u
variable {G : Type u} [Group G] [IsSimpleGroup G]
variable {F : Type} [Field F] [Finite F]
variable {p n : ℕ} [Fact p.Prime] [NeZero n]

/-- The source's ambient simplicity discharges the projective-model simplicity
premise. Geometric realization and image normality remain explicit. -/
theorem isPSU_four_of_exteriorRealization (hp : p ≠ 2)
    (e : G ≃* POmegaMinus 3 F)
    (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
    (hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F))
    (hN : (R.projectiveAction hcomm).range.Normal) : IsPSU G 4 (p ^ n) := by
  let : IsSimpleGroup (POmegaMinus 3 F) := e.symm.isSimpleGroup
  exact ⟨Extension p n, inferInstance, inferInstance, unitaryForm p n,
    card_extension p n, unitaryForm_conj p n,
    ⟨e.trans (R.projectiveEquiv_of_normal p n hcomm hp hN)⟩⟩

/-- The original odd minus-six model belongs to the PSU₄ branch at the same
fixed-field order. Ambient simplicity discharges the sole simplicity input. -/
theorem isPSU_four_of_isPOmegaMinus_three {q : ℕ} (ho : Odd q)
    (h : IsPOmegaMinus G 3 q) : IsPSU G 4 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  let : IsSimpleGroup (POmegaMinus 3 F) := e.symm.isSimpleGroup
  obtain ⟨E, hE, hEfin, J, hcard, hconj, ⟨f⟩⟩ :=
    exists_projectiveEquivPSU F (by simpa only [hc] using ho)
  exact ⟨E, hE, hEfin, J, hcard.trans (by rw [hc]),
    fun x => (hconj x).trans (by rw [hc]), ⟨e.trans f⟩⟩

end CFSG.Quasithin.ChapterA.Section02.SmallIsomorphisms
