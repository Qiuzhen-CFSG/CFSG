module

public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition.Source
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly

/-!
# G.2.4 with its projective recognition premise discharged

The universal field-four case of G.1.3 recognizes the actual upper quotient
constructed from the G.2.4 hypothesis. Substitution into the existing assembly
proves all eight clauses without a separate recognition input, preserving
the original subgroups, quotient maps, fixed spaces and order formulas.
The terminal branch retains precisely its two printed extra hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.3 and G.2.4, printed pp.327 and 334–335.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
namespace Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)

/-- All eight clauses of the original G.2.4, with G.1.3 proved on the
literal upper quotient rather than retained as an additional assumption. -/
theorem lemma_G_2_4_source :
    (D.star D.U = (D.star D.L₁).pCoreIn 2 ∧
      ∃ P : Sylow 2 (D.star D.L),
        (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) ∧
    (D.I g = D.L ⊔ D.U ∧
      (D.I g : Set G) = (D.L : Set G) * (D.U : Set G)) ∧
    (D.S g = D.W g ⊔ conjugate (D.W g) g ∧
      (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G)) ∧
    (D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
      D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
      (D.VL.subgroupOf (D.I g)).Normal ∧
      ((S₂ D g).subgroupOf (D.I g)).Normal ∧
      (S₂ D g : Set G) = (D.VL : Set G) * (D.U ⊓ conjugate D.U g : Subgroup G)) ∧
    ⁅S₂ D g, D.I g⁆ ≤ D.VL ∧
    (let := d.second_normal_in_core d.L_le_I
      ∃ (s : ℕ) (c : NaturalLayer D g F4 s d.L_le_I),
        IsCompl (upperImage D g (D.W g))
          (upperImage D g (conjugate (D.W g) g)) ∧
        upperImage D g (D.W g) = c.action.commonFixed (D.U.subgroupOf (D.I g)) ∧
        Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g)) ∧
    (⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U → D.L₁.pCoreIn 2 ≤ D.QH →
      D.I g = D.L ∧ D.S g = D.VL ∧ ChapterC.IsAlternatingBlock D.L 5 ∧
        D.U = D.L₁.pCoreIn 2 ∧ Nonempty (QuaternionCentralProductData D.U) ∧
        Nonempty (D.U ≃* QuaternionCentralProduct.Model)) :=
  d.lemma_G_2_4 Section01.SL2FourRecognition.recognitionInput

/-- The recognized natural layer and its two order formulas, including
the zero-multiplicity case, on the original G.2.4 subgroups. -/
theorem natural_layer_source :
    let := d.second_normal_in_core d.L_le_I
    ∃ (s : ℕ) (c : NaturalLayer D g F4 s d.L_le_I),
      IsCompl (upperImage D g (D.W g))
        (upperImage D g (conjugate (D.W g) g)) ∧
      upperImage D g (D.W g) = c.action.commonFixed (D.U.subgroupOf (D.I g)) ∧
      Nat.card (upperImage D g (D.W g)) = 2 ^ (2 * s) ∧
      Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g) ∧
      Nat.card (D.S g) = 2 ^ (4 * s + 4) * D.VL.relIndex (S₂ D g) :=
  d.source_natural_layer Section01.SL2FourRecognition.recognitionInput

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
