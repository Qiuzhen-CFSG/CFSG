module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.Alternating.theorem_5_2_3

/-!
# The permutation model is the involution centralizer in A10

The permutation (01)(23)(45)(67) has four two-cycles and two fixed points.
The alternating centralizer structure theorem identifies its cycle factor,
enlarged by an odd cycle rotation coupled with the swap of the fixed points,
with the full wreath product C2 wr S4. Its remaining factor is A2 and is
therefore trivial. This gives the actual intrinsic centralizer in A10.
The pointwise multiplicative equivalence below identifies the wreath product's
base with the published multiplicative binary function space, preserving the
inverse-coordinate permutation action.

This is the alternating local model in the remark on printed p.224 and
Section 1 of D. Held, "A Characterization of some multiply transitive
permutation groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756. The centralizer calculation uses the checked
involution structure underlying GLS, volume 3, Proposition 5.2.8(a).
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

open GLS3.Chapter5 CentralizerModels

/-- Moving the multiplicative type tag inside the function space identifies
the published permutation model with the standard involution wreath product. -/
@[expose] public def permutationModelEquivInvolutionWreath :
    PermutationModel ≃* InvolutionWreath 4 := by
  refine SemidirectProduct.congr (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 2)
    (MulEquiv.refl _) ?_
  intro s
  ext v i
  rfl

private theorem a10_cycle_count :
    Fintype.card a10Permutation.cycleFactorsFinset = 4 := by
  rw [Fintype.card_coe]
  decide +kernel

private theorem a10_fixed_count :
    Fintype.card (Function.fixedPoints a10Permutation) = 2 := by
  decide +kernel

private theorem a10_fixed_eq_centralizer :
    automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin 10)) a10Permutation) =
    a10Centralizer := by
  ext g
  change (MulAut.conjNormal a10Permutation) g = g ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subtype.ext_iff]
  change a10Permutation * g.val * a10Permutation⁻¹ = g.val ↔
    g.val * a10Permutation = a10Permutation * g.val
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem a10Centralizer_nonempty_equiv_wreath :
    Nonempty (a10Centralizer ≃* InvolutionWreath 4) := by
  classical
  have hx : orderOf a10Permutation = 2 :=
    (Subgroup.orderOf_coe a10Involution).trans a10Involution_order
  obtain ⟨R, L, H₁, H₂, t, hdecomp, _, _, _, _, _, _, _, _, ⟨e₂, _⟩,
    _, _, _, _, hfull⟩ := involutionAlternatingCentralizerCoreStructure 10 a10Permutation hx
  rw [a10_fixed_count] at e₂ hfull
  rw [a10_cycle_count] at hfull
  have hH₂ : H₂ = ⊥ := by
    have hcard : Nat.card H₂ = 1 := by
      rw [Nat.card_congr e₂.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact Subgroup.card_eq_one.mp hcard
  rw [hH₂, sup_bot_eq, a10_fixed_eq_centralizer] at hdecomp
  obtain ⟨⟨e₁⟩, _⟩ := hfull (by decide)
  exact ⟨(MulEquiv.subgroupCongr hdecomp).trans e₁⟩

/-- The ordinary binary permutation semidirect product is the actual
centralizer of (01)(23)(45)(67) in A10. -/
public noncomputable def permutationModelEquivA10Centralizer :
    PermutationModel ≃* a10Centralizer :=
  permutationModelEquivInvolutionWreath.trans
    (Classical.choice a10Centralizer_nonempty_equiv_wreath).symm

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
