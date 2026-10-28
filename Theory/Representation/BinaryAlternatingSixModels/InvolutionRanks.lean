module
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryAlternatingSixModels.Geometry
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.TensorInvolutionDisplacement

/-!
# Even-involution ranks in the actual binary S₆ models

A nontrivial four-dimensional binary A₆ representation has involution
rank two. The tensor displacement formula therefore gives rank eight
on the actual sixteen-dimensional tensor model. The complete S₆ catalogue
then identifies every nontrivial simple module with even-involution rank
at most two with one of the two literal natural models.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.967.
The companion chief-factor consumer descends the actual quotient action;
no dimension or model identification is assumed there.
-/

public section
open Representation Subgroup
open Representation.BinaryOffender.NaturalTensor
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule
namespace BinaryAlternatingSix

/-- An involution moves half of any nontrivial four-dimensional binary
A₆-module. This will rule out the sixteen-dimensional tensor constituent
in the case-one small fixed-index quotient. -/
theorem four_space_involution_rank
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A6 W) (hn : ∃ g, ρ g ≠ 1)
    (hd : Module.finrank (ZMod 2) W = 4)
    (a : A6) (ha : orderOf a = 2) : operatorFixedCodim (ρ a) = 2 := by
  have hl := AlternatingSixInvolutionDisplacement.displacement_lower_of_nontrivial ρ hn a ha
  have hs : ρ a * ρ a = 1 := by
    have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
    rw [← map_mul, ← pow_two, ha2, map_one]
  have hu := TensorInvolutionDisplacement.twice_displacement_le (ρ a) hs
  rw [hd] at hu
  change 2 ≤ operatorFixedCodim (ρ a) at hl
  omega



private theorem first_nontrivial : ∃ g : A6, firstAlternating g ≠ 1 := by
  by_contra! h
  apply first_has_no_line
  refine ⟨polarLine 0, polarLine_finrank 0, ?_⟩
  intro g _ v hv
  rw [h g]
  exact hv

private theorem second_nontrivial : ∃ g : A6, secondAlternating g ≠ 1 := by
  obtain ⟨g,hg⟩ := first_nontrivial
  refine ⟨alternatingDiagramAut.symm g, ?_⟩
  intro he
  apply hg
  change firstAlternating (alternatingDiagramAut (alternatingDiagramAut.symm g)) = 1 at he
  simpa using he

/-- Every even involution has displacement eight on the actual tensor
model, identified elsewhere with the duad--syntheme Steinberg module. -/
theorem tensor_even_involution_rank (a : S6)
    (ha : orderOf a = 2) (heven : a ∈ A6) : operatorFixedCodim (tensorAction a) = 8 := by
  let b : A6 := ⟨a,heven⟩
  have hb : orderOf b = 2 :=
    (orderOf_injective A6.subtype Subtype.coe_injective b).symm.trans ha
  have h1 := four_space_involution_rank firstAlternating first_nontrivial
    naturalModule_finrank b hb
  have h2 := four_space_involution_rank secondAlternating second_nontrivial
    naturalModule_finrank b hb
  have hs (ρ : Representation (ZMod 2) S6 NaturalModule) : ρ a * ρ a = 1 := by
    have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
    rw [← map_mul, ← pow_two, ha2, map_one]
  have ht := TensorInvolutionDisplacement.tensor_displacement_formula
    (firstNatural a) (secondNatural a) (hs firstNatural) (hs secondNatural)
  change operatorFixedCodim (tensorAction a) +
    2 * operatorFixedCodim (firstAlternating b) * operatorFixedCodim (secondAlternating b) =
    Module.finrank (ZMod 2) NaturalModule * operatorFixedCodim (firstAlternating b) +
    Module.finrank (ZMod 2) NaturalModule * operatorFixedCodim (secondAlternating b) at ht
  rw [h1,h2,naturalModule_finrank] at ht
  omega

/-- A nontrivial simple S₆ module with an even involution moving at most
two dimensions is one of the two literal natural models. -/
theorem natural_of_small_even_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) S6 W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (a : S6) (ha : orderOf a = 2) (heven : a ∈ A6)
    (hsmall : operatorFixedCodim (ρ a) ≤ 2) :
    Nonempty (ρ.Equiv firstNatural) ∨ Nonempty (ρ.Equiv secondNatural) := by
  rcases symmetric_classify ρ with he | he | he | he
  · obtain ⟨e⟩ := he
    exfalso
    apply hne
    ext g v
    apply e.toLinearEquiv.injective
    exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  · exact Or.inl he
  · exact Or.inr he
  · obtain ⟨e⟩ := he
    have heq := operatorFixedCodim_eq_of_equiv (ρ a) (tensorAction a) e.toLinearEquiv
      (fun v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap a v)
    rw [heq,tensor_even_involution_rank a ha heven] at hsmall
    omega
end BinaryAlternatingSix

