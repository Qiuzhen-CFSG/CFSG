module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalGeometry

/-!
# The normally generated factor inside an enlarged local component

Faithfulness identifies the cyclic subgroup with its induced action image;
the exceptional image of order three therefore forces corank two. The other
three-dimensional summand is a hyperplane in U. Normal generation inside the
two-residual gives a genuine subgroup with the full Frobenius image. When
that residual normalizes a containing component in C_G(V₂), this generated
subgroup lies in the component and proves C_V(L₂) = V₂, of corank three.

The construction of the containing component and its model classification
are separate from these deductions, and remain required for E.6.25.
Source: Aschbacher–Smith, E.6.25, printed pp.255–256 (PDF pp.266–267).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G] {M V U X : Subgroup G}

/-- Faithfulness identifies the cyclic subgroup with its actual automizer image. -/
theorem regularCyclicSection_card_image (hX : RegularCyclicSection M V U X) :
    Nat.card (inducedAutomizer V X) = Nat.card X := by
  have hXN : X ≤ normalizer (V : Set G) :=
    hX.contained.trans (inf_le_left.trans inf_le_right)
  let f : X →* inducedAutomizer V X :=
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hXN)).codRestrict _
      (fun x => ⟨⟨x, hXN x.property⟩, x.property, rfl⟩)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have he : V.normalizerMonoidHom ⟨x, hXN x.property⟩ = 1 :=
      congrArg (fun a : inducedAutomizer V X => (a.val : MulAut V)) hx
    have hc : (x : G) ∈ centralizer (V : Set G) := by
      have hk : (⟨x, hXN x.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker := he
      rwa [Subgroup.normalizerMonoidHom_ker] at hk
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hX.faithful ▸ (show (x : G) ∈ X ⊓ centralizer (V : Set G) from
      ⟨x.property, hc⟩))
  have hs : Function.Surjective f := by
    rintro ⟨a, n, hn, he⟩
    exact ⟨⟨n, hn⟩, Subtype.ext he⟩
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hi, hs⟩).toEquiv).symm

/-- The exceptional cyclic image has order three, hence the obstruction has corank two. -/
theorem exceptional_corank_eq_two (hX : RegularCyclicSection M V U X)
    (hc : Nat.card (inducedAutomizer V X) = 3) : subgroupCorank V U = 2 := by
  rw [regularCyclicSection_card_image hX, hX.card_eq] at hc
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  norm_num
  omega

variable [Finite G] [IsElementaryAbelian 2 V]

/-- In corank three, a contained corank-two subspace is a hyperplane over the smaller one. -/
theorem relativeIndex_eq_two_of_coranks {W : Subgroup G}
    (hWU : W ≤ U) (hUV : U ≤ V)
    (hW : subgroupCorank V W = 3) (hU : subgroupCorank V U = 2) :
    W.relIndex U = 2 := by
  have hwi : W.relIndex V = 2 ^ subgroupCorank V W := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact V.relIndex_eq_two_pow_quotient_finrank W
  have hui : U.relIndex V = 2 ^ subgroupCorank V U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact V.relIndex_eq_two_pow_quotient_finrank U
  have he := relIndex_mul_relIndex W U V hWU hUV
  rw [hwi, hui, hW, hU] at he
  omega

variable {K : GroupClass} {T : Sylow 2 G}

/-- The normally generated lift has the full factor image and fixes exactly V₂. -/
theorem generatedFactorLift_fixed_other (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (hC : Nat.card (inducedAutomizer V X) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf
      (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤) :
    V ⊓ centralizer (generatedFactorLift V X (D.factor D.distinguished) : Set G) =
      subspaceGroup (D.summand j) := by
  have hXN := hX.contained.trans (inf_le_left.trans inf_le_right)
  have hoX := regularCyclicSection_odd hX (by rw [exceptional_corank_eq_two hX hC]; decide)
  have hoB : Odd (Nat.card (D.factor D.distinguished)) := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Frobenius21.card_model]
    decide
  rw [← subspaceGroup_fixedSpace _
    ((generatedFactorLift_le V X _).trans (residualLift_le V _)),
    generatedFactorLift_image hXN D.contained hoX hoB hgen]
  rw [fixedSpace_factor_eq_other D
    (normalClosure_fixedSpace_eq_bot h hU hXN hX.fixed)
    (decomposition_spans h hU hXN hX.fixed D) D.distinguished j hij htwo]

/-- Actual containment of the normally generated lift forces the enlarged
component's fixed subgroup to equal V₂, and its corank to be three. -/
theorem containing_fixedSpace_eq_other (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (hC : Nat.card (inducedAutomizer V X) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf
      (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤)
    (hdim : Module.finrank (ZMod 2) (D.summand D.distinguished) = 3)
    (L₂ : Subgroup G) (hXL₂ : X ≤ L₂)
    (hL₂H : L₂ ≤ centralizer (subspaceGroup (D.summand j) : Set G))
    (hN : residualLift V (D.factor D.distinguished) ≤ normalizer (L₂ : Set G)) :
    generatedFactorLift V X (D.factor D.distinguished) ≤ L₂ ∧
      V ⊓ centralizer (L₂ : Set G) = subspaceGroup (D.summand j) ∧
      subgroupCorank V (V ⊓ centralizer (L₂ : Set G)) = 3 := by
  have hYL := generatedFactorLift_le_of_normalizes hXL₂ hN
  have hf := generatedFactorLift_fixed_other h hU hX D j hij htwo hC hmodel hgen
  have he : V ⊓ centralizer (L₂ : Set G) = subspaceGroup (D.summand j) := by
    apply le_antisymm
    · rw [← hf]
      exact inf_le_inf_left V (Subgroup.centralizer_le hYL)
    · exact le_inf (subspaceGroup_le _) (le_centralizer_iff.mpr hL₂H)
  refine ⟨hYL, he, ?_⟩
  rw [he]
  exact (corank_subspaceGroup_of_isCompl _ _
    (two_summands_isCompl h hU hX D j hij htwo)).trans hdim
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
