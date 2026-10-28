module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Theory.Representation.SL2FourNaturalOrbits.Model
import Mathlib.Tactic.Group

/-!
# Changing the marking of a linear–graph action on SL₃(4)

Every actual automorphism of SL₃(4) preserves the coset of linear conjugations
followed by inverse transpose. The GL₃ factor is retained, and the actor is
not required to have order two. The result is also proved over every finite
binary field of order greater than two.

On PSL₃, standard automorphism coverage and the matrix compatibility laws
factor the conjugator into linear, coefficient-field and graph actions.
For a linear–field conjugator with factors m and σ, the new matrix is
m σ(c) (m⁻¹)⁻ᵀ; a graph factor replaces c by c⁻ᵀ first. Both sides already
have explicit SL₃ actions. Perfectness of SL₃ makes its central-quotient
action faithful, so their equality on PSL₃ gives equality on SL₃. No lifting
existence for an arbitrary projective automorphism is assumed.

The final two theorems transport the literal relation a(g)t = t a(c g⁻ᵀ c⁻¹),
retaining t and using the new marking e.trans β. This discharges the universal
`GraphRemarking` premise of the natural-section/no-FF construction in the
SL₃(4) branch of Aschbacher–Smith 13.8.20, printed p.955 (PDF p.972).

Sources: GLS3, Theorem 2.5.12(a,e) and §2.7 in
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith, combined manuscript of
1 March 2004, `refs/quasithin.pdf`. The reused elementary perfectness theorem
retains its ATLAS attribution and license in
`Theory.AtlasPort.ExceptionalIsomorphisms.Elementary`.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.GraphRemarking
variable {F : Type*} [Field F]

private theorem semilinear_conj_graph (m c : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F m * fieldAction F σ) * (linearConj F c * graph F) *
        (linearConj F m * fieldAction F σ)⁻¹ =
      linearConj F (m * GeneralLinearGroup.map σ.toRingHom c *
        inverseTransposeGL F m⁻¹) * graph F := by
  calc
    _ = linearConj F m * (fieldAction F σ * linearConj F c) *
        graph F * (fieldAction F σ)⁻¹ * (linearConj F m)⁻¹ := by group
    _ = linearConj F m * linearConj F (GeneralLinearGroup.map σ.toRingHom c) *
        (fieldAction F σ * graph F) * (fieldAction F σ)⁻¹ *
        (linearConj F m)⁻¹ := by rw [field_linearConj]; group
    _ = linearConj F m * linearConj F (GeneralLinearGroup.map σ.toRingHom c) *
        graph F * (linearConj F m)⁻¹ := by rw [(field_commute_graph σ).eq]; group
    _ = _ := by
      rw [← map_inv, mul_assoc, graph_linearConj, ← mul_assoc, ← map_mul, ← map_mul]

private theorem projective_conj_graph (α : MulAut PSL(3,F))
    (hα : α ∈ standard F) (c : GL (Fin 3) F) :
    ∃ c' : GL (Fin 3) F,
      α * (linearConj F c * graph F) * α⁻¹ = linearConj F c' * graph F := by
  obtain ⟨m, σ, rfl | rfl⟩ :=
    Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization F
      field_linearConj graph_linearConj_exists field_commute_graph α hα
  · exact ⟨_, semilinear_conj_graph m c σ⟩
  · refine ⟨m * GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F c) *
        inverseTransposeGL F m⁻¹, ?_⟩
    calc
      _ = (linearConj F m * fieldAction F σ) * (graph F * linearConj F c) *
          (linearConj F m * fieldAction F σ)⁻¹ := by group
      _ = _ := by rw [graph_linearConj, semilinear_conj_graph]

private theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = Subgroup.quotientAut (Subgroup.center SL(3,F)) := by
    ext a x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) x
    change centerAction F a (QuotientGroup.mk y) = _
    rw [centerAction_mk, Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

private theorem graphSL_eq_inverseTranspose (g : SL(3,F)) :
    graphSL F g = SpecialLinearGroup.inverseTranspose g := by
  apply Subtype.ext
  exact (Matrix.adjugate_transpose g.val).symm

/-- Conjugation by any actual SL₃ automorphism preserves the full linear–graph
coset over a finite binary field of order greater than two. -/
theorem linear_graph_remarking_of_two_power_card [Finite F] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (β : MulAut SL(3,F)) (c : GL (Fin 3) F) :
    ∃ c' : GL (Fin 3) F, ∀ g : SL(3,F),
      β (linearConjSL F c (SpecialLinearGroup.inverseTranspose (β.symm g))) =
        linearConjSL F c' (SpecialLinearGroup.inverseTranspose g) := by
  have hcover := AutomorphismCoverage.standard_eq_top F hn hF
  obtain ⟨c', hc'⟩ := projective_conj_graph (centerAction F β)
    (hcover ▸ Subgroup.mem_top _) c
  have he : β * (linearConjSL F c * graphSL F) * β⁻¹ =
      linearConjSL F c' * graphSL F := by
    apply centerAction_injective
    simpa only [map_mul, map_inv, linearConj, MonoidHom.comp_apply, graph] using hc'
  refine ⟨c', fun g => ?_⟩
  simpa only [MulAut.mul_apply, MulAut.inv_apply, graphSL_eq_inverseTranspose] using
    MulEquiv.congr_fun he g

/-- The exact change-of-marking statement for the quadratic four-element field
used by the natural SL₃(4) representation. -/
theorem linear_graph_remarking
    (β : MulAut SL(3,Representation.SL2FourNatural.F))
    (c : GL (Fin 3) Representation.SL2FourNatural.F) :
    ∃ c' : GL (Fin 3) Representation.SL2FourNatural.F,
      ∀ g : SL(3,Representation.SL2FourNatural.F),
      β (linearConjSL Representation.SL2FourNatural.F c
        (SpecialLinearGroup.inverseTranspose (β.symm g))) =
      linearConjSL Representation.SL2FourNatural.F c'
        (SpecialLinearGroup.inverseTranspose g) := by
  apply linear_graph_remarking_of_two_power_card (n := 2) (by decide)
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
  decide

section Four
local notation "𝔽" => Representation.SL2FourNatural.F
variable {D K : Type*} [Monoid D] [Group K]

/-- Precomposing the marked homomorphism by β⁻¹ keeps the same ambient actor
and changes only the GL₃ correction in its graph relation. -/
theorem graph_relation_remarking (β : MulAut SL(3,𝔽))
    (a : SL(3,𝔽) →* D) (t : D) (c : GL (Fin 3) 𝔽)
    (ht : ∀ g, a g * t = t * a (linearConjSL 𝔽 c
      (SpecialLinearGroup.inverseTranspose g))) :
    ∃ c' : GL (Fin 3) 𝔽, ∀ g,
      (a.comp β.symm.toMonoidHom) g * t = t *
        (a.comp β.symm.toMonoidHom) (linearConjSL 𝔽 c'
          (SpecialLinearGroup.inverseTranspose g)) := by
  obtain ⟨c', hc'⟩ := linear_graph_remarking β c
  refine ⟨c', fun g => ?_⟩
  have he := congrArg β.symm (hc' g)
  rw [β.symm_apply_apply] at he
  change a (β.symm g) * t = t * a (β.symm _)
  rw [ht, he]

/-- The source convention e′ = e.trans β, with the literal embedding into the
ambient monoid. Apply a to the component inclusion to obtain the subgroup
relation used in the natural-section construction. -/
theorem graph_relation_trans (a : K →* D) (e : K ≃* SL(3,𝔽))
    (β : MulAut SL(3,𝔽)) (t : D) (c : GL (Fin 3) 𝔽)
    (ht : ∀ g, a (e.symm g) * t = t * a (e.symm
      (linearConjSL 𝔽 c (SpecialLinearGroup.inverseTranspose g)))) :
    ∃ c' : GL (Fin 3) 𝔽, ∀ g,
      a ((e.trans β).symm g) * t = t * a ((e.trans β).symm
        (linearConjSL 𝔽 c' (SpecialLinearGroup.inverseTranspose g))) := by
  exact graph_relation_remarking β (a.comp e.symm.toMonoidHom) t c ht

end Four
end Matrix.PSL3Even.GraphRemarking
