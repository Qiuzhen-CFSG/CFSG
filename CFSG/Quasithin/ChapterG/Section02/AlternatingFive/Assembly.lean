module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block

/-!
# Assembly of G.2.4

The starred Borel and orthogonal geometry prove clauses (1–5). They supply
every structural premise of the projective recognition and counting argument,
which constructs the natural upper layer in (6–7). That same layer discharges
the terminal branch's earlier-clause inputs, yielding the intrinsic A₅-block
and the quaternion central product in (8).

Only the genuine universal G.1.3 implication remains an earlier-source input;
its discharge belongs to the enclosing G.2 assembly. The actual orthogonal
module in the hypothesis and the natural SL₂(4) upper section stay distinct.
The quotient terms are images in S/S₂, not quotients assuming S₂≤W.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma G.2.4, printed pp.334–335, PDF pp.345–346.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
namespace Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

/-- Clauses (6–7), with all structural inputs proved from G.2.4's hypothesis.
The same multiplicity governs the literal W-image, U and S. -/
theorem source_natural_layer (hrec : RecognitionInput.{0,u} F4) :
    let := d.second_normal_in_core d.L_le_I
    ∃ (s : ℕ) (c : NaturalLayer D g F4 s d.L_le_I),
      IsCompl (upperImage D g (D.W g))
        (upperImage D g (conjugate (D.W g) g)) ∧
      upperImage D g (D.W g) = c.action.commonFixed (D.U.subgroupOf (D.I g)) ∧
      Nat.card (upperImage D g (D.W g)) = 2 ^ (2 * s) ∧
      Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g) ∧
      Nat.card (D.S g) = 2 ^ (4 * s + 4) * D.VL.relIndex (S₂ D g) :=
  d.natural_upper_layer_and_order hrec d.I_eq_LU d.S_eq_star_kernel
    d.S_eq_sup d.V_sup_conjugate d.VL_inf_U d.card_V d.W_index_four

/-- Construct the terminal branch's marked upper-module input. Neither
its natural coordinates nor its fixed-space or order identities are assumed. -/
theorem exists_earlierUpper (hrec : RecognitionInput.{0,u} F4) :
    let := d.second_normal_in_core d.L_le_I
    ∃ s : ℕ, Nonempty (Block.EarlierUpper D g d.earlierStructure F4 s) := by
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, c, hcompl, hfixed, _, horder, _⟩ := d.source_natural_layer hrec
  exact ⟨s, ⟨⟨c, hcompl, hfixed, horder⟩⟩⟩

/-- G.2.4(8), with no earlier-clause, core-collapse, block-recognition or
quaternion premise. The only extra hypotheses are the two printed ones. -/
theorem source_terminal_block (hrec : RecognitionInput.{0,u} F4)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) :
    D.I g = D.L ∧ D.S g = D.VL ∧ ChapterC.IsAlternatingBlock D.L 5 ∧
      D.U = D.L₁.pCoreIn 2 ∧ Nonempty (QuaternionCentralProductData D.U) ∧
      Nonempty (D.U ≃* QuaternionCentralProduct.Model) := by
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, ⟨e⟩⟩ := d.exists_earlierUpper hrec
  exact d.terminal_block d.earlierStructure e hfull hcore

/-- The source's Q₈² is Q₈∘Q₈: the factors in the original U meet in V₁,
and their multiplication induces the displayed diagonal-quotient equivalence. -/
theorem source_quaternion_presentation (hrec : RecognitionInput.{0,u} F4)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) :
    ∃ q : QuaternionCentralProductData D.U,
      (q.left ⊓ q.right).map D.U.subtype = D.V₁ ∧
      ∃ (eL : q.left ≃* QuaternionGroup 2) (eR : q.right ≃* QuaternionGroup 2)
        (f : QuaternionCentralProduct.Model ≃* D.U),
        ∀ x y : QuaternionGroup 2,
          f (QuotientGroup.mk' QuaternionCentralProduct.diagonalCenter (x, y)) =
            eL.symm x * eR.symm y := by
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, ⟨e⟩⟩ := d.exists_earlierUpper hrec
  exact d.terminal_quaternion_presentation d.earlierStructure e hfull hcore

/-- All eight clauses of G.2.4. The products are literal set products,
normality is relative to I, and (6) uses the actual images in S/S₂.
G.1.3 is the sole earlier-source premise retained by this assembly. -/
theorem lemma_G_2_4 (hrec : RecognitionInput.{0,u} F4) :
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
        Nonempty (D.U ≃* QuaternionCentralProduct.Model)) := by
  refine ⟨⟨d.star_U_eq_local_core, d.star_U_sylow⟩,
    ⟨d.I_eq_LU, d.I_product⟩, ⟨d.S_eq_sup, d.S_eq_product⟩,
    ⟨d.source_layers.1, le_sup_left, d.second_le_core d.L_le_I,
      d.source_layers.2.2.2.1, d.second_normal d.L_le_I, d.second_product d.L_le_I⟩,
    d.second_commutator d.L_le_I, ?_, d.source_terminal_block hrec⟩
  let := d.second_normal_in_core d.L_le_I
  obtain ⟨s, c, hcompl, hfixed, _, horder, _⟩ := d.source_natural_layer hrec
  exact ⟨s, c, hcompl, hfixed, horder⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
